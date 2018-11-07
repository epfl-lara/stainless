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

  private[this] def isCandidate(id: Identifier)(implicit symbols: s.Symbols): Boolean = {
    import s._
    val cd = symbols.getClass(id)
    cd.parents match {
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
    }
  }

  private[this] val constructorCache = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)
  private[this] def constructorID(id: Identifier)(implicit symbols: s.Symbols): Identifier =
    symbols.lookupClass(id).map { cd =>
      if (cd.parents.isEmpty && !(cd.flags contains s.IsAbstract)) constructorCache(cd.id)
      else cd.id
    }.get
    
  private[this] def constructors(id: Identifier)(implicit symbols: s.Symbols): Seq[Identifier] = {
    val cd = symbols.getClass(id)
    val classes = cd +: cd.descendants

    classes.filterNot(_.flags contains s.IsAbstract).map(_.id)
  }

  private[this] def isCaseObject(id: Identifier)(implicit symbols: s.Symbols): Boolean = {
    isCandidate(id) && (symbols.getClass(id).flags contains s.IsCaseObject)
  }

  private[this] val caseObject = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)
  private[this] val unapplyID = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)

  override protected final def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)
  protected final class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
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
        t.FunctionInvocation(caseObject(id), Seq(), Seq()).copiedFrom(e)

      case s.ClassConstructor(s.ClassType(id, tps), args) if isCandidate(id) =>
        t.ADT(constructorID(id), tps map transform, args map transform).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(pat: s.Pattern): t.Pattern = pat match {
      case s.ClassPattern(binder, s.ClassType(id, tps), subs) if isCandidate(id) =>
        t.ADTPattern(binder map transform, constructorID(id), tps map transform, subs map transform).copiedFrom(pat)
      case iop @ s.InstanceOfPattern(ob, tpe @ s.ClassType(id, tps)) if isCandidate(id) =>
        if (constructors(id) == Seq(id)) {
          val subs = tpe.tcd.fields.map(_ => t.WildcardPattern(None).copiedFrom(pat))
          t.ADTPattern(ob map transform, constructorID(id), tps map transform, subs).copiedFrom(iop)
        } else if (root(id) == id) {
          t.WildcardPattern(ob map transform).copiedFrom(iop)
        } else {
          t.UnapplyPattern(None, Seq(),
            unapplyID(id),
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
            t.IsConstructor(vd.toVariable, constructorID(cid)).copiedFrom(tpe)
          }).copiedFrom(tpe)).copiedFrom(tpe)
        }
      case _ => super.transform(tpe)
    }
  }

  private[this] def descendantKey(id: Identifier)(implicit symbols: s.Symbols): CacheKey =
    SetKey(
      (symbols.dependencies(id) + id)
        .flatMap(id => Set(id) ++ symbols.lookupClass(id).toSeq.flatMap { cd =>
          val rootCd = symbols.getClass(root(cd.id))
          Set(rootCd.id) ++ rootCd.descendants.map(_.id)
        })
    )

  // The function cache must consider the descendants of all classes on which the
  // function depends as they will determine which classes will be transformed into
  // sorts and which ones will not.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, context) => FunctionKey(fd) + descendantKey(fd.id)(context.symbols)
  )

  // If there are any input sorts in this phase, their transformation is simple
  override protected final val sortCache = new SimpleCache[s.ADTSort, SortResult]

  // The class cache must also consider all descendants of dependent classes as they
  // will again determine what will become a sort and what won't.
  // We must further depend on the synthetic OptionSort for the generated unapply function.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult]({
    // Note that we could use a more precise key here that determines whether the
    // option sort will be used by the class result, but this shouldn't be necessary
    (cd, context) => 
      val symbols = context.symbols
      ClassKey(cd) + descendantKey(cd.id)(symbols) + OptionSort.key(symbols)
  })

  override protected final def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected final def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  override protected final type ClassResult = Either[t.ClassDef, (Option[t.ADTSort], Seq[t.FunDef])]
  override protected final def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols = {
    classes.foldLeft(symbols) {
      case (symbols, Left(cd)) => symbols.withClasses(Seq(cd))
      case (symbols, Right((sort, fds))) => symbols.withSorts(sort.toSeq).withFunctions(fds)
    }
  }

  override protected final def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult = {
    import context.{t => _, s => _, _}
    if (isCandidate(cd.id)) {
      if (cd.parents.isEmpty) {
        val sortTparams = cd.tparams map (tpd => context.transform(tpd))
        val newSort = new t.ADTSort(
          cd.id,
          sortTparams,
          constructors(cd.id).map { cid =>
            val consCd = context.symbols.getClass(cid)
            val tpMap = (consCd.tparams.map(tpd => context.transform(tpd).tp) zip sortTparams.map(_.tp)).toMap
            new t.ADTConstructor(
              constructorID(cid),
              cd.id,
              consCd.fields map { vd =>
                val tvd = context.transform(vd)
                tvd.copy(tpe = t.typeOps.instantiateType(tvd.tpe, tpMap))
              }
            ).copiedFrom(consCd)
          },
          cd.flags filterNot (f => f == s.IsAbstract || f == s.IsSealed) map (f => context.transform(f))
        ).copiedFrom(cd)

        val functions = (cd +: cd.descendants).flatMap { cd =>
          import t.dsl._

          val objectFunction = if (isCaseObject(cd.id)) {
            val vd = t.ValDef.fresh("v", t.ADTType(root(cd.id), cd.typeArgs map (transform(_))).setPos(cd)).setPos(cd)
            val returnType = t.RefinementType(vd, t.IsConstructor(vd.toVariable, cd.id).setPos(cd)).setPos(cd)
            Some(mkFunDef(caseObject(cd.id), t.Inline, t.Derived(cd.id))()(_ => (
              Seq(),
              returnType,
              (_ => t.ADT(constructorID(cd.id), Seq(), Seq()).setPos(cd))
            )).setPos(cd))
          } else {
            None
          }

          import OptionSort._
          val cons = constructors(cd.id)
          val unapplyFunction = if (root(cd.id) != cd.id && cons != Seq(cd.id)) {
            Some(mkFunDef(unapplyID(cd.id), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))
                         (cd.typeArgs.map(_.id.name) : _*) { case tparams =>
              val base = T(root(cd.id))(tparams : _*)
              def condition(e: t.Expr): t.Expr = t.orJoin(cons.map(t.IsConstructor(e, _)))

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

          objectFunction.toSeq ++ unapplyFunction
        }

        Right((Some(newSort), functions))
      } else {
        Right((None, Seq()))
      }
    } else {
      Left(context.transform(cd))
    }
  }

  override protected final def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val newSymbols = super.extractSymbols(context, symbols)
      .withFunctions(OptionSort.functions(symbols))
      .withSorts(OptionSort.sorts(symbols))

      // println(newSymbols.asString(PrinterOptions.fromContext(self.context))

    val dependencies: Set[Identifier] =
      (symbols.functions.keySet ++ symbols.sorts.keySet ++ symbols.classes.keySet)
        .flatMap(id => newSymbols.dependencies(id) + id)

    val independentSymbols = t.NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.filter { fd =>
        dependencies(fd.id) ||
        // keep the introduced case object construction functions
        fd.flags.exists { case t.Derived(id) => dependencies(id) case _ => false }
      })
      .withSorts(newSymbols.sorts.values.toSeq.filter(sort => dependencies(sort.id)))
      .withClasses(newSymbols.classes.values.toSeq.filter(cd => dependencies(cd.id)))

    independentSymbols
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
