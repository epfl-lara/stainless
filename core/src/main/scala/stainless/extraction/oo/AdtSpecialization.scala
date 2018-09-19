/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait AdtSpecialization
  extends CachingPhase
     with SimpleFunctions
     with SimpleSorts
     with utils.SyntheticSorts { self =>

  val s: Trees
  val t: Trees

  private[this] def root(id: Identifier)(implicit symbols: s.Symbols): Identifier = {
    symbols.getClass(id).parents.map(ct => root(ct.id)).headOption.getOrElse(id)
  }

  private[this] val candidateCache = ExtractionCache[s.ClassDef, Boolean]()
  private[this] def isCandidate(id: Identifier)(implicit symbols: s.Symbols): Boolean = {
    import s._
    val cd = symbols.getClass(id)
    candidateCache.cached(cd, symbols)(cd.parents match {
      case Nil =>
        def rec(cd: s.ClassDef): Boolean = {
          val cs = cd.children
          (cd.parents.size <= 1) &&
          (cs forall rec) &&
          (cd.parents forall (_.tps == cd.typeArgs)) &&
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

  private class ClassInfo(
    val id: Identifier,
    val constructors: Seq[Identifier],
    val objectFunction: Option[Identifier],
    val unapplyFunction: Option[Identifier],
    val functions: Seq[t.FunDef],
    val sorts: Seq[t.ADTSort]
  )

  private[this] val infoCache = OptionSort.cached(ExtractionCache[s.ClassDef, ClassInfo]())
  private[this] val constructorCache = ExtractionCache[s.ClassDef, Identifier]()
  private[this] def classInfo(id: Identifier)(implicit context: TransformerContext): ClassInfo = {
    import t.dsl._
    import context.{s => _, t => _, _}

    val cd = context.symbols.getClass(id)
    infoCache.get.cached(cd, context.symbols) {
      assert(isCandidate(id))

      val classes = cd +: cd.descendants
      val extraConstructors: Seq[Identifier] = classes
        .filter(cd => (cd.flags contains s.IsAbstract) && !(cd.flags contains s.IsSealed))
        .map(cd => constructorCache.cached(cd, symbols)(FreshIdentifier("Open")))

      val constructors = classes.filterNot(_.flags contains s.IsAbstract).map(_.id) ++ extraConstructors

      val constructorId = if (cd.parents.isEmpty && !(cd.flags contains s.IsAbstract)) {
        cd.id.freshen
      } else {
        cd.id
      }

      val objectFunction = if (isCaseObject(id)) {
        val vd = t.ValDef.fresh("v", t.ADTType(root(id), cd.typeArgs map (tp => context.transform(tp))))
        val returnType = t.RefinementType(vd, t.IsConstructor(vd.toVariable, id))
        Some(mkFunDef(cd.id.freshen, t.Inline, t.Derived(cd.id))()(_ => (
          Seq(),
          returnType,
          (_ => t.ADT(constructorId, Seq(), Seq()).setPos(cd))
        )).setPos(cd))
      } else {
        None
      }

      import OptionSort._
      val unapplyFunction = if (root(id) != id && constructors != Seq(id)) {
        Some(mkFunDef(cd.id.freshen, t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))
                     (cd.typeArgs.map(_.id.name) : _*) { case tparams =>
          val base = T(root(id))(tparams : _*)
          def condition(e: t.Expr): t.Expr = t.orJoin(constructors.map(t.IsConstructor(e, _)))

          val vd = t.ValDef.fresh("v", base)
          val returnType = t.RefinementType(vd, condition(vd.toVariable))
          (Seq("x" :: base), T(option)(returnType), { case Seq(x) =>
            if_ (condition(x)) {
              C(some)(returnType)(x)
            } else_ {
              C(none)(returnType)()
            }
          })
        })
      } else {
        None
      }

      new ClassInfo(constructorId, constructors, objectFunction.map(_.id), unapplyFunction.map(_.id),
        objectFunction.toSeq ++ unapplyFunction ++ (if (unapplyFunction.nonEmpty) OptionSort.functions else Seq()),
        if (unapplyFunction.nonEmpty) OptionSort.sorts else Seq())
    }
  }

  private[this] def constructors(id: Identifier)(implicit context: TransformerContext): Seq[Identifier] = {
    classInfo(id).constructors
  }

  private[this] def constructorId(id: Identifier)(implicit context: TransformerContext): Identifier = {
    if (context.symbols.classes contains id) classInfo(id).id
    else id // This covers the injected open class identifiers
  }

  private[this] def objectFunction(id: Identifier)(implicit context: TransformerContext): Identifier = {
    assert(isCaseObject(id)(context.symbols))
    classInfo(id).objectFunction.get
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    protected implicit val implicitContext: TransformerContext = this

    override def transform(e: s.Expr): t.Expr = e match {
      case s.ClassSelector(expr, selector) => expr.getType match {
        case s.ClassType(id, tps) if isCandidate(id) =>
          val vd = t.ValDef.fresh("e", t.ADTType(root(id), tps map transform).copiedFrom(e)).copiedFrom(e)
          t.Let(vd, transform(expr),
            t.Annotated(t.ADTSelector(vd.toVariable, selector).copiedFrom(e), Seq(t.Unchecked)).copiedFrom(e)
          ).copiedFrom(e)
        case _ => super.transform(e)
      }

      case s.ClassConstructor(s.ClassType(id, Seq()), Seq()) if isCaseObject(id) =>
        t.FunctionInvocation(objectFunction(id), Seq(), Seq()).copiedFrom(e)

      case s.ClassConstructor(s.ClassType(id, tps), args) if isCandidate(id) =>
        t.ADT(constructorId(id), tps map transform, args map transform).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(pat: s.Pattern): t.Pattern = pat match {
      case s.ClassPattern(binder, s.ClassType(id, tps), subs) if isCandidate(id) =>
        t.ADTPattern(binder map transform, constructorId(id), tps map transform, subs map transform).copiedFrom(pat)
      case iop @ s.InstanceOfPattern(ob, tpe @ s.ClassType(id, tps)) if isCandidate(id) =>
        if (constructors(id) == Seq(id)) {
          val subs = tpe.tcd.fields.map(_ => t.WildcardPattern(None).copiedFrom(pat))
          t.ADTPattern(ob map transform, constructorId(id), tps map transform, subs).copiedFrom(iop)
        } else if (root(id) == id) {
          t.WildcardPattern(ob map transform).copiedFrom(iop)
        } else {
          t.UnapplyPattern(None, Seq(),
            classInfo(id).unapplyFunction.get,
            tps map transform,
            Seq(t.WildcardPattern(ob map transform).copiedFrom(iop))
          ).copiedFrom(iop)
        }
      case _ => super.transform(pat)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ClassType(id, tps) if isCandidate(id) =>
        if (id == root(id)) {
          t.ADTType(id, tps map transform).copiedFrom(tpe)
        } else {
          val vd = t.ValDef(FreshIdentifier("v"), t.ADTType(root(id), tps map transform).copiedFrom(tpe)).copiedFrom(tpe)
          t.RefinementType(vd, t.orJoin(constructors(id).map { cid =>
            t.IsConstructor(vd.toVariable, constructorId(cid)).copiedFrom(tpe)
          }).copiedFrom(tpe)).copiedFrom(tpe)
        }
      case _ => super.transform(tpe)
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  override protected type ClassResult = Either[t.ClassDef, (Seq[t.ADTSort], Seq[t.FunDef])]
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols = {
    classes.foldLeft(symbols) {
      case (symbols, Left(cd)) => symbols.withClasses(Seq(cd))
      case (symbols, Right((sorts, fds))) => symbols.withSorts(sorts).withFunctions(fds)
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
          constructors(cd.id)(context).map { cid =>
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

        val functions = cd.descendants.flatMap(cd => classInfo(cd.id)(context).functions).distinct
        val sorts = cd.descendants.flatMap(cd => classInfo(cd.id)(context).sorts).distinct
        Right((newSort +: sorts, functions))
      } else {
        Right((Seq(), Seq()))
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
  } = new {
    override val s: ts.type = ts
    override val t: tt.type = tt
  } with AdtSpecialization {
    override val context = ctx
  }
}
