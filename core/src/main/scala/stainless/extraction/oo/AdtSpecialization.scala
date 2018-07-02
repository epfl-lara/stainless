/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait AdtSpecialization extends CachingPhase with SimpleFunctions with SimpleSorts { self =>
  val s: Trees
  val t: Trees

  private[this] def root(id: Identifier)(implicit symbols: s.Symbols): Identifier = {
    symbols.getClass(id).parents.map(ct => root(ct.id)).headOption.getOrElse(id)
  }

  private[this] val candidateCache = new ExtractionCache[s.ClassDef, Boolean]
  private[this] def isCandidate(id: Identifier)(implicit symbols: s.Symbols): Boolean = {
    import s._
    val cd = symbols.getClass(id)
    candidateCache.cached(cd, symbols)(cd.parents match {
      case Nil =>
        def rec(cd: s.ClassDef): Boolean = {
          val cs = cd.children
          (cd.parents.size <= 1) &&
          (cs forall rec) &&
          ((cd.flags contains IsAbstract) || cs.isEmpty) &&
          (!(cd.flags contains IsAbstract) || cd.fields.isEmpty) &&
          (cd.typeArgs forall (tp => tp.isInvariant && !tp.flags.exists { case Bounds(_, _) => true case _ => false }))
        }
        rec(cd)
      case _ => isCandidate(root(cd.id))
    })
  }

  private[this] def isCaseObject(id: Identifier)(implicit symbols: s.Symbols): Boolean = {
    isCandidate(id) && (symbols.getClass(id).flags contains s.IsCaseObject)
  }

  private case class ClassInfo(constructors: Seq[Identifier], objectFunction: Option[t.FunDef], id: Identifier)
  private[this] val infoCache = new ExtractionCache[s.ClassDef, ClassInfo]
  private[this] def classInfo(id: Identifier)(implicit context: TransformerContext): ClassInfo = {
    import s._
    import context.{t => _, _}
    val cd = context.symbols.getClass(id)
    infoCache.cached(cd, context.symbols) {
      assert(isCandidate(id))

      val classes = cd +: cd.descendants
      val extraConstructor: Option[Identifier] =
        if (classes.exists(cd => (cd.flags contains IsAbstract) && !(cd.flags contains IsSealed))) {
          Some(FreshIdentifier("Open"))
        } else {
          None
        }

      val constructors = classes.filterNot(_.flags contains IsAbstract).map(_.id) ++ extraConstructor

      val constructorId = if (cd.parents.isEmpty && !(cd.flags contains IsAbstract)) {
        cd.id.freshen
      } else {
        cd.id
      }

      val objectFunction = if (isCaseObject(id)) {
        val vd = t.ValDef(FreshIdentifier("v"), t.ADTType(
          root(id),
          cd.typed.toType.tps.map(tpe => context.transform(tpe))
        ).copiedFrom(cd)).copiedFrom(cd)
        val returnTpe = t.RefinementType(vd, t.IsConstructor(vd.toVariable, constructorId).copiedFrom(cd)).copiedFrom(cd)
        Some(new t.FunDef(
          cd.id.freshen, Seq(), Seq(), returnTpe,
          t.ADT(constructorId, Seq(), Seq()).setPos(cd), Seq(t.Inline, t.Derived(cd.id))
        ).setPos(cd))
      } else {
        None
      }

      ClassInfo(constructors, objectFunction, constructorId)
    }
  }

  private[this] def constructors(id: Identifier)(implicit context: TransformerContext): Seq[Identifier] = {
    classInfo(id).constructors
  }

  private[this] def constructorId(id: Identifier)(implicit context: TransformerContext): Identifier = {
    if (context.symbols.classes contains id) classInfo(id).id
    else id // This covers the injected open class identifiers
  }

  private[this] def objectFunction(id: Identifier)(implicit context: TransformerContext): t.FunDef = {
    assert(isCaseObject(id)(context.symbols))
    classInfo(id).objectFunction.get
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    protected implicit val implicitContext: TransformerContext = this

    override def transform(e: s.Expr): t.Expr = e match {
      case s.ClassSelector(expr, selector) => symbols.widen(expr.getType) match {
        case s.ClassType(id, tps) if isCandidate(id) =>
          val vd = t.ValDef.fresh("e", t.ADTType(root(id), tps map transform).copiedFrom(e)).copiedFrom(e)
          t.Let(vd, transform(expr),
            t.Annotated(t.ADTSelector(vd.toVariable, selector).copiedFrom(e), Seq(t.Unchecked)).copiedFrom(e)
          ).copiedFrom(e)
        case _ => super.transform(e)
      }

      case s.ClassConstructor(s.ClassType(id, Seq()), Seq()) if isCaseObject(id) =>
        t.FunctionInvocation(objectFunction(id)(this).id, Seq(), Seq()).copiedFrom(e)

      case s.ClassConstructor(s.ClassType(id, tps), args) if isCandidate(id) =>
        t.ADT(constructorId(id), tps map transform, args map transform).copiedFrom(e)

      case s.MatchExpr(scrut, cases) =>
        t.MatchExpr(transform(scrut), cases map { case cse @ s.MatchCase(pat, optGuard, rhs) =>
          var guards: Seq[s.Expr] = Nil
          val newPat = s.patternOps.postMap {
            case iop @ s.InstanceOfPattern(ob, tpe @ s.ClassType(id, tps)) if isCandidate(id) =>
              if (constructors(id) == Set(id)) {
                val subs = tpe.tcd.fields.map(_ => s.WildcardPattern(None).copiedFrom(pat))
                Some(s.ADTPattern(ob, constructorId(id), tps, subs).copiedFrom(iop))
              } else if (root(id) == id) {
                Some(s.WildcardPattern(ob).copiedFrom(iop))
              } else {
                val v = ob getOrElse s.ValDef(
                  FreshIdentifier("v"),
                  s.ADTType(root(id), tps).copiedFrom(iop)
                ).copiedFrom(iop)

                guards :+= s.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
                  s.IsConstructor(v.toVariable, constructorId(cid)).copiedFrom(iop)
                })
                Some(s.WildcardPattern(Some(v)).copiedFrom(iop))
              }
            case _ => None
          } (pat)

          val newGuard = (optGuard ++ guards).toSeq match {
            case Nil => None
            case seq => Some(s.andJoin(seq)).filterNot(_ == s.BooleanLiteral(true))
          }

          t.MatchCase(transform(newPat), newGuard map transform, transform(rhs)).copiedFrom(cse)
        }).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(pat: s.Pattern): t.Pattern = pat match {
      case s.ClassPattern(binder, s.ClassType(id, tps), subs) if isCandidate(id) =>
        t.ADTPattern(binder map transform, constructorId(id), tps map transform, subs map transform).copiedFrom(pat)
      case _ => super.transform(pat)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ClassType(id, tps) if isCandidate(id) =>
        if (id == root(id)) {
          t.ADTType(id, tps map transform).copiedFrom(tpe)
        } else {
          val vd = t.ValDef(FreshIdentifier("v"), t.ADTType(root(id), tps map transform).copiedFrom(tpe)).copiedFrom(tpe)
          t.RefinementType(vd, t.orJoin(constructors(id).toSeq.sortBy(_.name).map { cid =>
            t.IsConstructor(vd.toVariable, constructorId(cid)).copiedFrom(tpe)
          }).copiedFrom(tpe)).copiedFrom(tpe)
        }
      case _ => super.transform(tpe)
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  override protected type ClassResult = Either[t.ClassDef, (Option[t.ADTSort], Seq[t.FunDef])]
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols = {
    classes.foldLeft(symbols) {
      case (symbols, Left(cd)) => symbols.withClasses(Seq(cd))
      case (symbols, Right((optSort, optFd))) => symbols.withSorts(optSort.toSeq).withFunctions(optFd.toSeq)
    }
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult = {
    import context.{t => _, s => _, _}
    if (isCandidate(cd.id)) {
      if (cd.parents.isEmpty) {
        val sortTparams = cd.tparams map (tpd => context.transform(tpd))
        val newSort = new t.ADTSort(
          cd.id,
          sortTparams,
          constructors(cd.id)(context).toSeq.sortBy(_.name).map { cid =>
            if (context.symbols.classes contains cid) {
              val consCd = context.symbols.getClass(cid)
              val tpMap = (consCd.tparams.map(tpd => context.transform(tpd).tp) zip sortTparams.map(_.tp)).toMap
              new t.ADTConstructor(
                constructorId(cid)(context),
                cd.id,
                consCd.fields map { vd =>
                  val tvd = context.transform(vd)
                  tvd.copy(tpe = t.typeOps.instantiateType(tvd.tpe, tpMap))
                }
              ).copiedFrom(consCd)
            } else { // injected open constructor
              val field = t.ValDef(FreshIdentifier("x"), t.IntegerType().copiedFrom(cd)).copiedFrom(cd)
              new t.ADTConstructor(cid, cd.id, Seq(field)).copiedFrom(cd)
            }
          },
          cd.flags filterNot (f => f == s.IsAbstract || f == s.IsSealed) map (f => context.transform(f))
        ).copiedFrom(cd)

        val objectFunctions = cd.descendants.filter(cd => isCaseObject(cd.id)).map(cd => objectFunction(cd.id)(context))
        Right((Some(newSort), objectFunctions))
      } else {
        Right((None, Seq()))
      }
    } else {
      Left(context.transform(cd))
    }
  }
}

object AdtSpecialization {
  def apply(ts: Trees, tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new AdtSpecialization {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
