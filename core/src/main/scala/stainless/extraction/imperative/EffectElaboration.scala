/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

trait EffectElaboration
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with RefTransform { self =>
  val s: Trees
  val t: s.type
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, context) => getDependencyKey(fd.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult](
    (sort, context) => getDependencyKey(sort.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult](
    (cd, context) => ClassKey(cd) + OptionSort.key(context.symbols)
  )

  override protected type FunctionResult = t.FunDef
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[t.FunDef]): t.Symbols =
    symbols.withFunctions(functions)

  override protected final type ClassResult = (t.ClassDef, Option[t.FunDef])
  override protected final def registerClasses(symbols: t.Symbols,
      classResults: Seq[ClassResult]): t.Symbols = {
    val (classes, unapplyFds) = classResults.unzip
    symbols.withClasses(classes).withFunctions(unapplyFds.flatten)
  }

  protected class TransformerContext(val symbols: Symbols) extends RefTransformContext

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  override protected def extractSymbols(tctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    // We filter out the definitions related to AnyHeapRef since they are only needed for infering which
    // types live in the heap
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.toSeq)
      .withClasses(symbols.classes.values.filterNot(cd => cd.flags.exists(_.name == "anyHeapRef")).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)
      
    super.extractSymbols(tctx, newSymbols)
      .withSorts(Seq(heapRefSort) ++ OptionSort.sorts(newSymbols))
      .withFunctions(OptionSort.functions(newSymbols))
  }

  override protected def extractFunction(tctx: TransformerContext, fd: FunDef): FunDef =
    (new tctx.FunRefTransformer).transform(fd)

  override protected def extractSort(tctx: TransformerContext, sort: ADTSort): ADTSort =
    tctx.typeOnlyRefTransformer.transform(sort)

  override protected def extractClass(tctx: TransformerContext, cd: ClassDef): ClassResult =
    (tctx.typeOnlyRefTransformer.transform(cd), tctx.makeClassUnapply(cd))
}

object EffectElaboration {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new EffectElaboration {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}

/** The actual Ref transformation **/

trait RefTransform extends oo.CachingPhase with utils.SyntheticSorts { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._

  /* Heap encoding */

  private[this] lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)

  /* The transformer */

  protected type TransformerContext <: RefTransformContext

  trait RefTransformContext { context: TransformerContext =>
    implicit val symbols: s.Symbols
    import symbols.{ livesInHeap, touchesHeap }

    lazy val EmptyHeap = FiniteMap(Seq(), UnitLiteral(), HeapRefType, AnyType())

    // This caches the effect level for the function definitions
    lazy val effectLevel = new utils.ConcurrentCached[Identifier, exprOps.EffectLevel]({ id =>
      exprOps.getEffectLevel(symbols.getFunction(id))
    })

    private def freshStateParam(): ValDef = "heap0" :: HeapType

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }
    def classTypeInHeap(ct: ClassType): ClassType =
      ClassType(ct.id, ct.tps.map(typeOnlyRefTransformer.transform)).copiedFrom(ct)

    def makeClassUnapply(cd: ClassDef): Option[FunDef] = {
      if (!livesInHeap(cd.typed.toType))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        (Seq("heap" :: HeapType, "x" :: HeapRefType), T(option)(objTpe), { case Seq(heap, x) =>
          if_ (IsInstanceOf(MapApply(heap, x), objTpe)) {
            C(some)(objTpe)(AsInstanceOf(MapApply(heap, x), objTpe))
          } else_ {
            C(none)(objTpe)()
          }
        })
      })
    }

    // Reduce all mutation to assignments of a local heap variable
    // TODO: Handle mutable types other than classes
    abstract class RefTransformer extends oo.DefinitionTransformer {
      val s: self.s.type = self.s
      val t: self.s.type = self.s

      override def transform(tpe: Type, env: Env): Type = tpe match {
        case ct: ClassType if livesInHeap(ct) =>
          HeapRefType
        case FunctionType(_, _) =>
          val FunctionType(from, to) = super.transform(tpe, env)
          FunctionType(HeapType +: from, T(to, HeapType))
        // TODO: PiType
        case _ =>
          super.transform(tpe, env)
      }

      override def transform(cd: ClassDef): ClassDef = {
        val env = initEnv
        // FIXME: Transform type arguments in parents?

        val newParents = cd.parents.filter {
          case AnyHeapRef() => false
          case _ => true
        }

        new ClassDef(
          transform(cd.id, env),
          cd.tparams.map(transform(_, env)),
          newParents,
          cd.fields.map(transform(_, env)),
          cd.flags.map(transform(_, env))
        ).copiedFrom(cd)
      }
    }

    object typeOnlyRefTransformer extends RefTransformer {
      override final type Env = Unit
      override final val initEnv: Unit = ()

      def transform(tpe: Type): Type = transform(tpe, ())
      def transform(vd: ValDef): ValDef = transform(vd, ())
      def transform(td: TypeParameterDef): TypeParameterDef = transform(td, ())
      def transform(flag: Flag): Flag = transform(flag, ())
    }

    class FunRefTransformer extends RefTransformer {
      import exprOps._

      val HeapRefSet: Type = SetType(HeapRefType)
      val EmptyHeapRefSet: Expr = FiniteSet(Seq.empty, HeapRefType)

      private lazy val dummyHeapVd: ValDef = "dummyHeap" :: HeapRefSet
      private val readSetVd: ValDef = "readSet" :: HeapRefSet
      private val writeSetVd: ValDef = "writeSet" :: HeapRefSet

      case class Env(writeAllowed: Boolean, updateSets: Boolean, heapVdOpt: Option[ValDef]) {
        def expectHeapVd(pos: Position, usage: String) =
          heapVdOpt getOrElse {
            self.context.reporter.error(pos, s"Cannot use effectful construct ($usage) here")
            dummyHeapVd
          }
      }
      def initEnv: Env = ???  // unused
      def specEnv(heapVdOpt: Option[ValDef]) =
        Env(writeAllowed = false, updateSets = false, heapVdOpt = heapVdOpt)
      def bodyEnv(writeAllowed: Boolean, heapVdOpt: Option[ValDef]) =
        Env(writeAllowed, updateSets = true, heapVdOpt = heapVdOpt)

      /**
       * Given an optional set of read expressions, and an input heap, projects the heap along
       * the read variables. The projection is conservative so that if no read clause is given,
       * everything is assumed to be read.
       */
      def projectHeap(subst: Map[ValDef, Expr], reads: Option[Expr], heapVd: ValDef): Expr =
        reads
          .map(r => MapMerge(transform(replaceFromSymbols(subst, r), specEnv(Some(heapVd))),
                             heapVd.toVariable, EmptyHeap))
          .getOrElse(heapVd.toVariable)

      /**
       * Given an optional set of modified exprssions and input and ouptut heaps, unprojects the
       * heap along the modified variables. The projection is conservative so that if no modifies
       * clause is given, everything is assumed to be modified.
       */
      def unprojectHeap(subst: Map[ValDef, Expr], modifies: Option[Expr],
                        inputHeapVd: ValDef, outputHeap: Expr): Expr =
        modifies
          .map(m => MapMerge(transform(replaceFromSymbols(subst, m), specEnv(Some(inputHeapVd))),
                             outputHeap, inputHeapVd.toVariable))
          .getOrElse(outputHeap)

      def valueFromHeap(recv: Expr, objTpe: ClassType, heapVd: ValDef, fromE: Expr): Expr = {
        val app = MapApply(heapVd.toVariable, recv).copiedFrom(fromE)
        val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
        val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
        Assume(iio, aio).copiedFrom(fromE)
      }

      override def transform(e: Expr, env: Env): Expr = e match {
        // Shallow equality is transformed into value equality on the erased trees
        case ShallowEquals(e1, e2) =>
          Equals(transform(e1, env), transform(e2, env))

        case Equals(e1, e2) =>
          if (touchesHeap(e1.getType) || touchesHeap(e2.getType))
            self.context.reporter.error(e.getPos, "Cannot compare two expressions containing references by value")
          Equals(transform(e1, env), transform(e1, env))

        case ClassConstructor(ct, args) if livesInHeap(ct) =>
          /*
          // TODO: Add mechanism to keep multiple freshly allocated objects apart
          val ref = Choose("ref" :: HeapRefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: HeapRefType, ref) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform)).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform)).copiedFrom(e)
            let("alloc" :: UnitType(), MapUpdated(TheHeap, ref, value).copiedFrom(e)) { _ =>
              ref
            }
          }
          */
          ???

        case ClassSelector(recv, field) if livesInHeap(recv.getType) =>
          val heapVd = env.expectHeapVd(e.getPos, "read from heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            ClassSelector(valueFromHeap(recvRef, objTpe, heapVd, e), field).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) if livesInHeap(recv.getType) =>
          if (!env.writeAllowed)
            self.context.reporter.error(e.getPos, "Can't modify heap in read-only function")

          val heapVd = env.expectHeapVd(e.getPos, "write to heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val oldObj = valueFromHeap(recvRef, objTpe, heapVd, e)
            let("oldObj" :: objTpe, oldObj) { oldObj =>
              val newCt = objTpe.asInstanceOf[ClassType]
              val newArgs = newCt.tcd.fields.map {
                case vd if vd.id == field => transform(value, env)
                case vd => ClassSelector(oldObj, vd.id).copiedFrom(e)
              }
              val newObj = ClassConstructor(newCt, newArgs).copiedFrom(e)
              val newHeap = MapUpdated(heapVd.toVariable, recvRef, newObj).copiedFrom(e)
              Assignment(heapVd.toVariable, newHeap).copiedFrom(e)
            }
          }

        case IsInstanceOf(recv, tpe) if livesInHeap(tpe) =>
          val heapVd = env.expectHeapVd(e.getPos, "runtime type-check on heap object")
          val ct = tpe.asInstanceOf[ClassType]
          val app = MapApply(heapVd.toVariable, transform(recv, env)).copiedFrom(e)
          IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)

        case fi @ FunctionInvocation(id, targs, vargs) =>
          val targs1 = targs.map(transform(_, env))
          val vargs1 = vargs.map(transform(_, env))

          effectLevel(id) match {
            case None =>
              FunctionInvocation(id, targs1, vargs1).copiedFrom(e)

            case Some(writes) =>
              val heapVd = env.expectHeapVd(e.getPos, "effectful function call")

              // TODO: Only translate arguments once. This makes the substitution below a bit more
              // as we have to substitute the local bindings with the old type (to trigger the
              // correct ref transformation).
              val subst = (fi.tfd.params zip vargs).toMap
              val (reads, modifies) = heapContractsOf(fi.tfd.fullBody)
              val projected = projectHeap(subst, reads, heapVd)
              val call = FunctionInvocation(id, targs1, projected +: vargs1).copiedFrom(e)

              if (writes) {
                // If the callee reads and modifies the state, we need to unproject the heap that
                // it returned and update the local heap variable.
                val resTpe = T(typeOnlyRefTransformer.transform(fi.tfd.returnType), HeapType)
                let("res" :: resTpe, call) { res =>
                  val unprojected = unprojectHeap(subst, modifies, heapVd, res._2)
                  Block(Seq(Assignment(heapVd.toVariable, unprojected)),
                    res._1)
                }
              } else {
                // If the callee only reads from but does not write to the heap, we merely project.
                call
              }
          }

        case _ => super.transform(e, env)
      }

      override def transform(pat: Pattern, env: Env): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if livesInHeap(ct) =>
          val newClassPat = ClassPattern(
            None,
            classTypeInHeap(ct),
            subPats.map(transform(_, env))
          ).copiedFrom(pat)
          UnapplyPattern(
            binder.map(transform(_, env)),
            Seq(),
            unapplyId(ct.id),
            ct.tps.map(transform(_, env)),
            Seq(newClassPat)
          ).copiedFrom(pat)
        case _ =>
          super.transform(pat, env)
      }

      override def transform(fd: FunDef): FunDef = {
        val level = effectLevel(fd.id)
        val reads = level.isDefined
        val writes = level.getOrElse(false)

        val heapVdOpt0 = if (reads) Some(freshStateParam()) else None
        val newParams = heapVdOpt0.toSeq ++ fd.params.map(typeOnlyRefTransformer.transform)
        val newReturnType = {
          val newReturnType1 = typeOnlyRefTransformer.transform(fd.returnType)
          if (writes) T(newReturnType1, HeapType) else newReturnType1
        }

        val (specs, bodyOpt) = deconstructSpecs(fd.fullBody)

        def transformPost(post: Expr, resVd: ValDef, valueVd: ValDef,
                          heapVdOpt0: Option[ValDef], heapVdOpt1: Option[ValDef]): Expr =
        {
          val replaceRes = resVd != valueVd
          val post1 = postMap {
            case v: Variable if replaceRes && v.id == resVd.id =>
              Some(valueVd.toVariable.copiedFrom(v))
            case Old(e) =>
              Some(transform(e, specEnv(heapVdOpt0)))
            case _ =>
              None
          }(post)
          transform(post1, specEnv(heapVdOpt1))
        }

        // TODO: Add readSet and writeSet instrumentation for specs
        val newSpecs = specs.collect {
          case Precondition(expr) =>
            Precondition(transform(expr, specEnv(heapVdOpt0)))

          case Measure(expr) =>
            Measure(transform(expr, specEnv(heapVdOpt0)))

          case Postcondition(lam @ Lambda(Seq(resVd), post)) =>
            val (resVd1, post1) = if (writes) {
              val valueVd: ValDef = "resV" :: resVd.tpe
              val heapVd1: ValDef = "heap1" :: HeapType
              val resVd1 = resVd.copy(tpe = T(resVd.tpe, HeapType))
              val post1 = Let(valueVd, resVd1.toVariable._1,
                Let(heapVd1, resVd1.toVariable._2,
                  transformPost(post, resVd, valueVd, heapVdOpt0, Some(heapVd1))))
              (resVd1, post1)
            } else {
              (resVd, transformPost(post, resVd, resVd, heapVdOpt0, heapVdOpt0))
            }
            Postcondition(Lambda(Seq(resVd1), post1).copiedFrom(lam))
        }

        val newBodyOpt: Option[Expr] = bodyOpt.map { body =>
          val newBody1 = if (writes) {
            val heapVd: ValDef = "heap" :: HeapType
            val innerNewBody = transform(body,
              bodyEnv(writeAllowed = true, heapVdOpt = Some(heapVd)))
            LetVar(writeSetVd, EmptyHeapRefSet,
              LetVar(heapVd, heapVdOpt0.get.toVariable,
                E(innerNewBody, heapVd.toVariable)))
          } else {
            transform(body, bodyEnv(writeAllowed = false, heapVdOpt = heapVdOpt0))
          }
          LetVar(readSetVd, EmptyHeapRefSet, newBody1)
        }
        val newBody = reconstructSpecs(newSpecs, newBodyOpt, newReturnType)

        new FunDef(
          fd.id,
          fd.tparams.map(typeOnlyRefTransformer.transform),
          newParams,
          newReturnType,
          newBody,
          fd.flags.map(typeOnlyRefTransformer.transform)
        ).copiedFrom(fd)
      }
    } // << FunRefTransformer
  }
}
