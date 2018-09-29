
package stainless
package extraction
package methods

import inox.utils.Position

trait MethodLifting extends oo.ExtractionPipeline with oo.ExtractionCaches { self =>
  val s: Trees
  val t: oo.Trees
  import s._

  private[this] def isAccessor(fd: FunDef): Boolean =
    fd.flags exists { case IsAccessor(_) => true case _ => false }

  // The function cache must consider all direct overrides of the current function.
  // Note that we actually use the set of transitive overrides here as computing
  // the set of direct overrides is significantly more expensive and shouldn't improve
  // the cache hit rate that much.
  private[this] final val funCache = new CustomCache[s.FunDef, t.FunDef]({ (fd, symbols) =>
    new DependencyKey(fd.id, fd.flags
      .collectFirst { case s.IsMethodOf(id) => symbols.getClass(id) }.toSeq
      .flatMap { cd =>
        val descendants = cd.descendants(symbols)
        val descendantIds = descendants.map(_.id).toSet

        val isInvariant = fd.flags contains s.IsInvariant

        def symbolOf(fd: s.FunDef): Symbol = fd.id.asInstanceOf[SymbolIdentifier].symbol

        symbols.functions.values
          .filter(_.flags exists { case s.IsMethodOf(id) => descendantIds(id) case _ => false })
          .filter { ofd =>
            if (isInvariant) ofd.flags contains s.IsInvariant
            else symbolOf(ofd) == symbolOf(fd) // casts are sound after checking `IsMethodOf`
          }.map(FunctionKey(_, symbols): CacheKey).toSet
      }.toSet)
  })

  // The class cache must consider all direct overrides of a potential invariant function
  // attached to the class.
  // Note that we could again use the set of transitive overrides here instead of all invariants.
  private[this] final val classCache = new CustomCache[s.ClassDef, (t.ClassDef, Option[t.FunDef])]({
    (cd, symbols) =>
      val ids = cd.descendants(symbols).map(_.id).toSet + cd.id

      val invariants = symbols.functions.values.filter { fd =>
        (fd.flags contains s.IsInvariant) &&
        (fd.flags exists { case s.IsMethodOf(id) => ids(id) case _ => false })
      }.map(FunctionKey(_, symbols) : CacheKey).toSet

      new DependencyKey(cd.id, invariants)
  })

  private case class FunOverride(cid: Identifier, fid: Option[Identifier], children: Seq[FunOverride])

  private[this] object identity extends oo.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  private class BaseTransformer(symbols: s.Symbols) extends oo.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t

    override def transform(e: s.Expr): t.Expr = e match {
      case s.MethodInvocation(rec, id, tps, args) =>
        val ct @ s.ClassType(_, _) = rec.getType(symbols)
        val cid = symbols.getFunction(id).flags.collectFirst { case s.IsMethodOf(cid) => cid }.get
        val tcd = (ct.tcd(symbols) +: ct.tcd(symbols).ancestors).find(_.id == cid).get
        t.FunctionInvocation(id, (tcd.tps ++ tps) map transform, (rec +: args) map transform).copiedFrom(e)

      case _ => super.transform(e)
    }
  }

  override final def extract(symbols: s.Symbols): t.Symbols = {
    assert(symbols.sorts.isEmpty,
      "Unexpected sorts in method lifting: " + symbols.sorts.keys.map(_.asString).mkString(", "))

    val classes = new scala.collection.mutable.ListBuffer[t.ClassDef]
    val functions = new scala.collection.mutable.ListBuffer[t.FunDef]

    val default = new BaseTransformer(symbols)

    for (cd <- symbols.classes.values) {
      val (invariant, functionToOverrides) = metadata(cd.id)(symbols)

      def transformMethod(fd: FunDef)(syms: Symbols): t.FunDef = {
        val o = functionToOverrides(fd.id)
        makeFunction(o.cid, fd.id, o.children)(syms)
      }

      val funs = cd.methods(symbols)
        .map(symbols.functions)
        .map { fd =>
          funCache.cached(fd, symbols)(transformMethod(fd)(symbols))
        }

      functions ++= funs

      val inv = invariant map { inv =>
        funCache.cached(inv, symbols)(transformMethod(inv)(symbols.withFunctions(Seq(inv))))
      }

      val (cls, fun) = classCache.cached(cd, symbols) {
        val cls = identity.transform(cd.copy(flags = cd.flags ++ invariant.map(fd => HasADTInvariant(fd.id))))
        (cls, inv)
      }

      classes += cls
      functions ++= fun
    }

    functions ++= symbols.functions.values
      .filterNot(_.flags exists { case IsMethodOf(_) => true case _ => false })
      .map { fd =>
        funCache.cached(fd, symbols)(default.transform(fd))
      }

    t.NoSymbols.withFunctions(functions.toSeq).withClasses(classes.toSeq)
  }

  private[this] type Metadata = (Option[s.FunDef], Map[Identifier, FunOverride])
  private[this] def metadata(cid: Identifier)(symbols: s.Symbols): Metadata = {
    def firstSymbol(cid: Identifier, vd: ValDef): Option[Symbol] = {
      val cd = symbols.getClass(cid)
      cd.methods(symbols).find { id =>
        val fd = symbols.getFunction(id)
        fd.tparams.isEmpty && fd.params.isEmpty && fd.id.name == vd.id.name && !isAccessor(fd)
      }.map(_.symbol).orElse(cd.parents.reverse.view.flatMap(ct => firstSymbol(ct.id, vd)).headOption)
    }

    val overrides: Map[Symbol, FunOverride] = {
      def rec(id: Identifier): Map[Symbol, FunOverride] = {
        val cd = symbols.getClass(id)
        val children = cd.children(symbols)
        val ctrees = children.map(ccd => rec(ccd.id))

        val newOverrides = cd.methods(symbols).map { fid =>
          fid.symbol -> FunOverride(id, Some(fid), ctrees.flatMap(_.get(fid.symbol)))
        }.toMap

        val noOverrides = ctrees.flatMap(_.keys.toSet).filterNot(newOverrides contains _).map {
          sym => sym -> FunOverride(id, None, ctrees.flatMap(_.get(sym)))
        }

        newOverrides ++ noOverrides
      }

      rec(cid)
    }

    val funs: Map[Symbol, Map[Identifier, FunOverride]] = {
      def rec(fo: FunOverride): Map[Identifier, FunOverride] = {
        val FunOverride(_, fid, children) = fo
        children.flatMap(rec).toMap ++ fid.map(_ -> fo)
      }

      overrides.map { case (sym, o) => sym -> rec(o) }
    }

    val invariantOverride = overrides
      .map { case (sym, o) => (o, funs(sym).toList.filter(p => symbols.getFunction(p._1).flags contains IsInvariant)) }
      .collectFirst { case (o: FunOverride, fs) if fs.nonEmpty => (o, fs) }

    val invariant = invariantOverride.map {
      case (o, ((id, FunOverride(_, optFid, _))) :: rest) if o.fid.isEmpty =>
        new FunDef(
          id.freshen,
          Seq.empty,
          Seq.empty,
          BooleanType(),
          BooleanLiteral(true),
          Seq(IsInvariant, IsMethodOf(cid))
        ).setPos(optFid match {
          case Some(fid) => symbols.getFunction(fid).getPos
          case None => symbols.getClass(cid).getPos
        })
      case (o, _) =>
        symbols.getFunction(o.fid.get)
    }

    val mappings = funs.flatMap(_._2) ++
      (invariantOverride zip invariant).map { case ((o, _), fd) => fd.id -> o.copy(fid = Some(fd.id)) }

    (invariant, mappings)
  }

  private[this] def makeFunction(cid: Identifier, fid: Identifier, cos: Seq[FunOverride])(symbols: s.Symbols): t.FunDef = {
    val cd = symbols.getClass(cid)
    val fd = symbols.getFunction(fid)
    val tpSeq = symbols.freshenTypeParams(cd.typeArgs).map { tp =>
      tp.copy(flags = tp.flags.filter { case Variance(_) => false case _ => true }).copiedFrom(tp)
    }
    val tpMap = (cd.typeArgs zip tpSeq).toMap

    val tcd = s.ClassType(cid, tpSeq).tcd(symbols).copiedFrom(cd)
    val arg = t.ValDef(FreshIdentifier("thiss"), identity.transform(tcd.toType)).copiedFrom(tcd)

    object transformer extends BaseTransformer(symbols) {
      override def transform(e: s.Expr): t.Expr = e match {
        case s.This(ct) => arg.toVariable
        case _ => super.transform(e)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case tp: s.TypeParameter if tpMap contains tp => super.transform(tpMap(tp))
        case _ => super.transform(tpe)
      }
    }

    def firstOverrides(fo: FunOverride): Seq[(Identifier, Either[FunDef, ValDef])] = fo match {
      case FunOverride(cid, Some(id), _) => Seq(cid -> Left(symbols.getFunction(id)))
      case FunOverride(_, _, children) => children.toSeq.flatMap(firstOverrides)
    }

    val subCalls = (for (co <- cos) yield {
      firstOverrides(co).map { case (cid, either) =>
        val descendant = tcd.descendants.find(_.id == cid).get
        val descType = identity.transform(descendant.toType).asInstanceOf[t.ClassType]
        val thiss = t.Annotated(t.AsInstanceOf(arg.toVariable, descType).copiedFrom(arg), Seq(t.Unchecked))

        def wrap(e: t.Expr, tpe: s.Type, expected: s.Type): t.Expr =
          if (symbols.isSubtypeOf(tpe, expected)) e
          else t.AsInstanceOf(e, transformer.transform(expected)).copiedFrom(e)

        val (tpe, expr) = either match {
          case Left(nfd) =>
            val ntpMap = descendant.tpSubst ++ (nfd.typeArgs zip fd.typeArgs)
            val args = (fd.params zip nfd.params).map { case (vd1, vd2) =>
              wrap(
                transformer.transform(vd1.toVariable),
                s.typeOps.instantiateType(vd1.tpe, tpMap),
                s.typeOps.instantiateType(vd2.tpe, ntpMap)
              )
            }
            (
              s.typeOps.instantiateType(nfd.returnType, ntpMap),
              t.FunctionInvocation(
                nfd.id,
                descType.tps ++ fd.tparams.map(tdef => transformer.transform(tdef.tp)),
                thiss +: args
              ).copiedFrom(fd)
            )
          case Right(vd) => (
            descendant.fields.find(_.id == vd.id).get.tpe,
            t.ClassSelector(thiss, vd.id).copiedFrom(fd)
          )
        }

        val expectedType = s.typeOps.instantiateType(fd.returnType, tpMap)
        (t.IsInstanceOf(arg.toVariable, descType).copiedFrom(arg), wrap(expr, tpe, expectedType))
      }
    }).flatten

    val returnType = transformer.transform(fd.returnType)

    val notFullyOverriden: Boolean = !(cd.flags contains IsSealed) || {
      def rec(fo: FunOverride): Boolean = fo match {
        case FunOverride(_, Some(_), _) => true
        case FunOverride(_, _, children) => children.forall(rec)
      }

      val coMap = cos.map(co => co.cid -> co).toMap
      cd.children(symbols).exists {
        ccd => !(coMap contains ccd.id) || !rec(coMap(ccd.id))
      }
    }

    val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)(symbols)

    val (conds, elze) = if (subCalls.isEmpty || notFullyOverriden) {
      val elze = body match {
        case Some(body) => transformer.transform(body)
        case None => t.NoTree(returnType).copiedFrom(fd.fullBody)
      }
      (subCalls, elze)
    } else {
      val conds :+ ((_, elze: t.Expr)) = subCalls
      (conds, elze)
    }

    val newSpecs = specs.map(_.map(t)(transformer.transform(_)))
    val dispatchBody = conds.foldRight(elze) { case ((cond, res), elze) =>
      t.IfExpr(cond, res, elze).setPos(Position.between(cond.getPos, elze.getPos))
    }

    val newBody = if (!(fd.flags contains IsInvariant)) dispatchBody else {
      // If `fd` is an invariant, we need to conjoin both the constructor's and parent's invariants,
      // otherwise we would only end up the checking the former.
      t.and(dispatchBody, elze.copiedFrom(dispatchBody))
    }

    val fullBody = t.exprOps.reconstructSpecs(newSpecs, Some(newBody), returnType)

    new t.FunDef(
      fd.id,
      (tpSeq.map(s.TypeParameterDef(_)) ++ fd.tparams) map transformer.transform,
      arg +: (fd.params map transformer.transform),
      returnType,
      fullBody,
      fd.flags filter {
        case s.IsMethodOf(_) | s.IsInvariant => false
        case _ => true
      } map transformer.transform
    ).copiedFrom(fd)
  }
}

object MethodLifting {
  def apply(ts: Trees, tt: oo.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new MethodLifting {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
