
package stainless
package extraction
package methods

import inox.utils.Position

class MethodLifting(override val s: Trees, override val t: oo.Trees)
                   (using override val context: inox.Context)
  extends oo.ExtractionContext
     with oo.ExtractionCaches { self =>

  import s._

  override protected final type TransformerContext = Symbols
  override protected final def getContext(symbols: s.Symbols) = symbols

  // The function cache must consider all direct overrides of the current function.
  // Note that we actually use the set of transitive overrides here as computing
  // the set of direct overrides is significantly more expensive and shouldn't improve
  // the cache hit rate that much.
  private[this] final val funCache = new ExtractionCache[s.FunDef, t.FunDef]({ (fd, symbols) =>
    FunctionKey(fd) + SetKey(fd.flags
      .collectFirst { case s.IsMethodOf(id) => symbols.getClass(id) }.toSeq
      .flatMap { cd =>
        val descendants = cd.descendants(using symbols)
        val descendantIds = descendants.map(_.id).toSet

        val isInvariant = fd.isInvariant

        def symbolOf(fd: s.FunDef): Symbol = fd.id.asInstanceOf[SymbolIdentifier].symbol

        symbols.functions.values
          .filter(_.flags exists { case s.IsMethodOf(id) => descendantIds(id) case _ => false })
          .filter { ofd =>
            if (isInvariant) ofd.isInvariant
            else symbolOf(ofd) == symbolOf(fd) // casts are sound after checking `IsMethodOf`
          }.map(FunctionKey(_): CacheKey).toSet
      }.toSet)
  })

  // The class cache must consider all direct overrides of potential invariants function attached to the class.
  // Note that we could again use the set of transitive overrides here instead of all invariants.
  private[this] final val classCache = new ExtractionCache[s.ClassDef, (t.ClassDef, Seq[t.FunDef])]({
    (cd, symbols) =>
      val ids = cd.descendants(using symbols).map(_.id).toSet + cd.id

      val invariants = symbols.functions.values.filter { fd =>
        (fd.flags contains s.IsInvariant) &&
        (fd.flags exists { case s.IsMethodOf(id) => ids(id) case _ => false })
      }.map(FunctionKey(_)).toSet

      ClassKey(cd) + SetKey(invariants)
  })

  private[this] final val typeDefCache = new ExtractionCache[s.TypeDef, t.TypeDef]({
    (td, symbols) => TypeDefKey(td)
  })

  private case class Override(cid: Identifier, fid: Option[Identifier], children: Seq[Override])

  private[this] class IdentityImpl(override val s: self.s.type, override val t: self.t.type)
    extends oo.ConcreteTreeTransformer(s, t)

  private[this] val identity = new IdentityImpl(self.s, self.t)

  private class BaseTransformer(override val s: self.s.type,
                                override val t: self.t.type,
                                val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) {
    def this(symbols: self.s.Symbols) = this(self.s, self.t, symbols)

    override def transform(e: s.Expr): t.Expr = e match {
      case s.MethodInvocation(rec, id, tps, args) =>
        val ct = rec.getType(using symbols).asInstanceOf[s.ClassType]
        val cid = symbols.getFunction(id).flags.collectFirst { case s.IsMethodOf(cid) => cid }.get
        val tcd = (ct.tcd(using symbols) +: ct.tcd(using symbols).ancestors).find(_.id == cid).get
        t.FunctionInvocation(id, (tcd.tps ++ tps) map transform, (rec +: args) map transform).copiedFrom(e)

      case _ => super.transform(e)
    }
  }

  override final def extract(symbols: s.Symbols): t.Symbols = {
    assert(symbols.sorts.isEmpty,
      "Unexpected sorts in method lifting: " + symbols.sorts.keys.map(_.asString).mkString(", "))

    val classes = new scala.collection.mutable.ListBuffer[t.ClassDef]
    val functions = new scala.collection.mutable.ListBuffer[t.FunDef]
    val typeDefs = new scala.collection.mutable.ListBuffer[t.TypeDef]

    val default = new BaseTransformer(symbols)

    for (cd <- symbols.classes.values) {
      val (invariants, functionToOverrides) = metadata(cd.id)(symbols)

      def transformMethod(fd: FunDef)(syms: Symbols): t.FunDef = {
        val o = functionToOverrides(fd.id)
        makeFunction(o.cid, fd.id, o.children)(syms)
      }

      val funs = cd.methods(using symbols)
        .map(symbols.functions)
        .map { fd =>
          funCache.cached(fd, symbols)(transformMethod(fd)(symbols))
        }

      functions ++= funs

      val invs = invariants map { inv =>
        funCache.cached(inv, symbols)(transformMethod(inv)(symbols.withFunctions(Seq(inv))))
      }

      val (cls, fun) = classCache.cached(cd, symbols) {
        val cls = identity.transform(cd.copy(flags = cd.flags ++ invariants.map(fd => HasADTInvariant(fd.id))))
        (cls, invs)
      }

      classes += cls
      functions ++= fun
    }

    functions ++= symbols.functions.values
      .filterNot(_.flags exists { case IsMethodOf(_) => true case _ => false })
      .map { fd =>
        funCache.cached(fd, symbols)(default.transform(fd))
      }

    for (td <- symbols.typeDefs.values) {
      typeDefs += typeDefCache.cached(td, symbols)(identity.transform(td))
    }

    t.NoSymbols.withFunctions(functions.toSeq).withClasses(classes.toSeq).withTypeDefs(typeDefs.toSeq)
  }

  private[this] type Metadata = (Seq[s.FunDef], Map[Identifier, Override])
  private[this] def metadata(cid: Identifier)(symbols: s.Symbols): Metadata = {
    val overrides: Map[Symbol, Override] = {
      def rec(id: Identifier): Map[Symbol, Override] = {
        val cd = symbols.getClass(id)
        val children = cd.children(using symbols)
        val ctrees = children.map(ccd => rec(ccd.id))

        val newOverrides = cd.methods(using symbols).map { fid =>
          fid.symbol -> Override(id, Some(fid), ctrees.flatMap(_.get(fid.symbol)))
        }.toMap

        val noOverrides = ctrees.flatMap(_.keys.toSet).filterNot(newOverrides contains _).map {
          sym => sym -> Override(id, None, ctrees.flatMap(_.get(sym)))
        }

        newOverrides ++ noOverrides
      }

      rec(cid)
    }

    val funs: Map[Symbol, Map[Identifier, Override]] = {
      def rec(fo: Override): Map[Identifier, Override] = {
        val Override(_, fid, children) = fo
        children.flatMap(rec).toMap ++ fid.map(_ -> fo)
      }

      overrides.map { case (sym, o) => sym -> rec(o) }
    }

    val invariantOverrides = overrides
      .map { case (sym, o) => (o, funs(sym).toList.filter(p => symbols.getFunction(p._1).flags contains IsInvariant)) }
      .collect { case (o: Override, fs) if fs.nonEmpty => (o, fs) }
      .toSeq

    val invariants = invariantOverrides.map {
      case (o, ((id, Override(_, optFid, _))) :: rest) if o.fid.isEmpty =>
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
      (invariantOverrides zip invariants).map { case ((o, _), fd) => fd.id -> o.copy(fid = Some(fd.id)) }

    (invariants, mappings)
  }

  private[this] def makeFunction(cid: Identifier, fid: Identifier, cos: Seq[Override])(symbols: s.Symbols): t.FunDef = {
    val cd = symbols.getClass(cid)
    val fd = symbols.getFunction(fid)
    val tpSeq = exprOps.freshenTypeParams(cd.typeArgs).map { tp =>
      tp.copy(flags = tp.flags.filter { case Variance(_) => false case _ => true }).copiedFrom(tp)
    }
    val tpMap = (cd.typeArgs zip tpSeq).toMap

    val ct = s.ClassType(cid, tpSeq).copiedFrom(cd)
    val tcd = ct.tcd(using symbols)
    val arg = t.ValDef(FreshIdentifier("thiss"), identity.transform(ct)).copiedFrom(cd)

    object transformer extends BaseTransformer(symbols) {
      override def transform(e: self.s.Expr): self.t.Expr = e match {
        case self.s.This(ct) => arg.toVariable
        case _ => super.transform(e)
      }

      override def transform(tpe: self.s.Type): self.t.Type = tpe match {
        case tp: self.s.TypeParameter if tpMap contains tp => super.transform(tpMap(tp))
        case _ => super.transform(tpe)
      }
    }

    def firstOverrides(fo: Override): Seq[(Identifier, FunDef)] = fo match {
      case Override(cid, Some(id), _) => Seq(cid -> symbols.getFunction(id))
      case Override(_, _, children) => children.flatMap(firstOverrides)
    }

    val subCalls = (for (co <- cos) yield {
      firstOverrides(co).map { case (cid, nfd) =>
        val descendant = tcd.descendants.find(_.id == cid).get
        val descType = identity.transform(descendant.toType.copiedFrom(nfd)).asInstanceOf[t.ClassType]

        def unchecked(expr: t.Expr): t.Expr = t.Annotated(expr, Seq(t.DropVCs)).copiedFrom(expr)
        val thiss = unchecked(t.AsInstanceOf(arg.toVariable, descType).copiedFrom(arg))

        def wrap(e: t.Expr, tpe: s.Type, expected: s.Type): t.Expr =
          if (symbols.isSubtypeOf(tpe, expected)) e else (e match {
            case v: t.Variable =>
              val expectedType = transformer.transform(expected.getType(using symbols))
              t.Assume(t.IsInstanceOf(e, expectedType).copiedFrom(e),
                unchecked(t.AsInstanceOf(e, expectedType).copiedFrom(e))).copiedFrom(e)
            case _ =>
              val vd = t.ValDef.fresh("x", transformer.transform(tpe), true).copiedFrom(e)
              val expectedType = transformer.transform(expected.getType(using symbols))
              t.Let(vd, e,
                t.Assume(t.IsInstanceOf(vd.toVariable, expectedType).copiedFrom(e),
                  unchecked(t.AsInstanceOf(vd.toVariable, expectedType).copiedFrom(e))).copiedFrom(e))
          })

        val (tpe, expr) = {
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
        }

        val expectedType = s.typeOps.instantiateType(fd.returnType, tpMap)
        (t.IsInstanceOf(arg.toVariable, descType).copiedFrom(arg), wrap(expr, tpe, expectedType))
      }
    }).flatten

    val returnType = transformer.transform(fd.returnType)

    val notFullyOverriden: Boolean = !(cd.flags contains IsSealed) || {
      def rec(fo: Override): Boolean = fo match {
        case Override(_, Some(_), _) => true
        case Override(_, _, children) => children.forall(rec)
      }

      val coMap = cos.map(co => co.cid -> co).toMap
      cd.children(using symbols).exists {
        ccd => !(coMap contains ccd.id) || !rec(coMap(ccd.id))
      }
    }

    val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)

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

    val newSpecs = specs.map(_.transform(transformer))
    val dispatchBody = conds.foldRight(elze) { case ((cond, res), elze) =>
      t.IfExpr(cond, res, elze).setPos(Position.between(cond.getPos, elze.getPos))
    }

    val fullBody = t.exprOps.reconstructSpecs(newSpecs, Some(dispatchBody), returnType)

    // a lifted method is derived from the methods that (first) override it
    val derivedFrom = cos.flatMap(o => firstOverrides(o).map(_._2))
    val derivedFlags = derivedFrom.map(fd => t.Derived(Some(fd.id)))
    val isAccessor = derivedFrom.nonEmpty && derivedFrom.forall(_.isAccessor)
    val accessorFlag = if (isAccessor) Some(t.Annotation("accessor", Seq.empty)) else None
    val filteredFlags = fd.flags filter {
        case s.IsMethodOf(_) | s.FieldDefPosition(_) => false
        case _ => true
      } map transformer.transform

    // we add the @inlineInvariant and @inline flags to invariant methods whose
    // class (or one descendant, or one ancestor) is annotated by @inlineInvariant
    val inlineInvariantFlags =
      if (fd.isInvariant &&
         (cd.descendants(using symbols) ++ cd.ancestors(using symbols).map(_.cd) :+ cd)
          .exists(_.flags.contains(InlineInvariant)))
        Seq(t.InlineInvariant, t.Inline)
      else
        Seq()

    new t.FunDef(
      fd.id,
      (tpSeq.map(s.TypeParameterDef(_)) ++ fd.tparams) map transformer.transform,
      arg +: (fd.params map transformer.transform),
      returnType,
      fullBody,
      (filteredFlags ++ derivedFlags ++ accessorFlag ++ inlineInvariantFlags).distinct
    ).copiedFrom(fd)
  }
}

object MethodLifting {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends MethodLifting(s, t)
    new Impl(trees, trees)
  }
}
