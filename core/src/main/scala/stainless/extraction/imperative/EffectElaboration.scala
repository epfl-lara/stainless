/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

object optCheckHeapContracts extends inox.FlagOptionDef("check-heap-contracts", true)

// TODO(gsps): Ghost annotations are currently unchecked. Should be able to reuse `GhostChecker`.
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
    (fd, context) => getDependencyKey(fd.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult](
    (sort, context) => getDependencyKey(sort.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult](
    (cd, context) => ClassKey(cd) + OptionSort.key(using context.symbols)
  )

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[FunctionResult]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected final type ClassResult = (t.ClassDef, Option[t.FunDef])
  override protected final def registerClasses(symbols: t.Symbols,
      classResults: Seq[ClassResult]): t.Symbols = {
    val (classes, unapplyFds) = classResults.unzip
    symbols.withClasses(classes).withFunctions(unapplyFds.flatten)
  }

  protected class TransformerContext(val symbols: Symbols) extends RefTransformContext

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  override protected def extractSymbols(tctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val isOldImperative = !context.options.findOptionOrDefault(optFullImperative)

    val anyHeapRefCdOpt = AnyHeapRefType.classDefOpt(using symbols)
    val heapCdOpt = HeapType.classDefOpt(using symbols)

    def shouldDrop(defn: Definition): Boolean =
      (
        anyHeapRefCdOpt.isDefined && symbols.dependsOn(defn.id, anyHeapRefCdOpt.get.id) ||
        heapCdOpt.isDefined && symbols.dependsOn(defn.id, heapCdOpt.get.id)
      ) && (isOldImperative || defn.flags.contains(Library))

    // We filter out the definitions related to AnyHeapRef and Heap.
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.filterNot(shouldDrop).toSeq)
      .withClasses(symbols.classes.values.filterNot(shouldDrop).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    // If we're not using the new imperative phase, we're done.
    if (isOldImperative)
      return newSymbols

    super.extractSymbols(tctx, newSymbols)
      .withSorts(Seq(heapRefSort) ++ OptionSort.sorts(using newSymbols))
      .withFunctions(Seq(dummyHeap) ++ OptionSort.functions(using newSymbols))
  }

  override protected def extractFunction(tctx: TransformerContext, fd: FunDef): FunctionResult =
    tctx.transformFun(fd)

  override protected def extractSort(tctx: TransformerContext, sort: ADTSort): ADTSort =
    tctx.typeOnlyRefTransformer.transform(sort)

  override protected def extractClass(tctx: TransformerContext, cd: ClassDef): ClassResult =
    (tctx.typeOnlyRefTransformer.transform(cd), tctx.makeClassUnapply(cd))
}

object EffectElaboration {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type)(using override val context: inox.Context) extends EffectElaboration
    new Impl(trees, trees)
  }
}

/** The actual Ref transformation **/

trait RefTransform
  extends oo.CachingPhase
     with utils.SyntheticSorts
     with HeapASTExtractors { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._

  lazy val checkHeapContracts = self.context.options.findOptionOrDefault(optCheckHeapContracts)

  /* Heap encoding */

  protected lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)
  protected lazy val shimId = new utils.ConcurrentCached[Identifier, Identifier](
    id => FreshIdentifier(s"${id.name}__shim")
  )

  /* The transformer */

  protected type TransformerContext <: RefTransformContext

  trait RefTransformContext { context: TransformerContext =>
    val symbols: s.Symbols
    import symbols.given

    lazy val HeapRefSetType: Type = SetType(HeapRefType)
    lazy val EmptyHeapRefSet: Expr = FiniteSet(Seq.empty, HeapRefType)

    // This caches whether types live in the heap or not
    lazy val erasesToHeapRef = new utils.ConcurrentCached[Type, Boolean](computeErasesToHeapRef(_))

    protected lazy val effectLevel = new utils.ConcurrentCached[Identifier, exprOps.EffectLevel]({
      id => exprOps.getEffectLevel(symbols.getFunction(id))
    })

    private def computeErasesToHeapRef(tpe: Type): Boolean = tpe match {
      case AnyHeapRefType() => true
      // We lookup the parents through the cache so that the hierarchy is traversed at most once
      case ct: ClassType => ct.tcd.parents.exists(a => erasesToHeapRef(a.toType))
      case _ => false
    }

    private def freshStateParam(): ValDef = "heap0" :: HeapMapType
    private def freshRefSetVd(name: String): ValDef = name :: HeapRefSetType

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }

    def unchecked(expr: Expr): Expr = Annotated(expr, Seq(DropVCs)).copiedFrom(expr)

    def classTypeInHeap(ct: ClassType): ClassType =
      ClassType(ct.id, ct.tps.map(typeOnlyRefTransformer.transform)).copiedFrom(ct)

    def makeClassUnapply(cd: ClassDef): Option[FunDef] = {
      if (!erasesToHeapRef(cd.typed.toType))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        // NOTE: Here we allow `readsDom` to be `None` to allow any access and `Some(dom)`
        //   to restrict reads to `dom`.
        (
          Seq("heap" :: HeapMapType, "readsDom" :: T(option)(HeapRefSetType), "x" :: HeapRefType),
          T(option)(objTpe),
          { case Seq(heap, readsDom, x) =>
            Require(
              Or(
                E(isEmpty)(HeapRefSetType)(readsDom),
                ElementOfSet(x, E(get)(HeapRefSetType)(readsDom))),
              if_ (IsInstanceOf(MapApply(heap, x), objTpe)) {
                C(some)(objTpe)(AsInstanceOf(MapApply(heap, x), objTpe))
              } else_ {
                C(none)(objTpe)()
              }
            )
          }
        )
      } .copiedFrom(cd))
    }

    // Reduce all mutation to assignments of a local heap variable
    // TODO: Handle mutable types other than classes
    abstract class RefTransformer(override val s: self.s.type, override val t: self.s.type)
      extends oo.DefinitionTransformer {

      def this() = this(self.s, self.s)

      override def transform(tpe: Type, env: Env): Type = tpe match {
        case HeapType() =>
          HeapMapType
        case ct: ClassType if erasesToHeapRef(ct) =>
          HeapRefType
        // case FunctionType(_, _) =>
        //   val FunctionType(from, to) = super.transform(tpe, env)
        //   FunctionType(HeapMapType +: from, T(to, HeapMapType))
        // TODO: PiType
        case _ =>
          super.transform(tpe, env)
      }

      override def transform(cd: ClassDef): ClassDef = {
        val env = initEnv
        // FIXME: Transform type arguments in parents?

        val newParents = cd.parents.filter {
          case AnyHeapRefType() => false
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

    // FIXME: This is probably a bad idea, since we might encounter dependent types.
    object typeOnlyRefTransformer extends RefTransformer {
      override final type Env = Unit
      override final val initEnv: Unit = ()

      def transform(tpe: Type): Type = transform(tpe, ())
      def transform(vd: ValDef): ValDef = transform(vd, ())
      def transform(td: TypeParameterDef): TypeParameterDef = transform(td, ())
      def transform(flag: Flag): Flag = transform(flag, ())
    }

    object funRefTransformer extends RefTransformer {
      private lazy val dummyHeapVd: ValDef = "dummyHeap" :: HeapMapType

      // Provides bindings to heap, reads and modifies domains.
      // For reads and modifies, None=disallowed, Some(None)=anything, Some(Some(v))=restricted.
       case class Env(
        readsVdOptOpt: Option[Option[ValDef]],
        modifiesVdOptOpt: Option[Option[ValDef]],
        heapVdOpt: Option[ValDef])
      {
        def expectHeapVd(pos: Position, usage: String) =
          heapVdOpt getOrElse {
            self.context.reporter.error(pos, s"Cannot use heap-accessing construct ($usage) here")
            dummyHeapVd
          }

        def expectReadsV(pos: Position, usage: String): Option[Expr] =
          readsVdOptOpt.map(_.map(_.toVariable)) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a reads clause")
            None
          }

        def expectModifiesV(pos: Position, usage: String): Option[Expr] =
          modifiesVdOptOpt.map(_.map(_.toVariable)) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a modifies clause")
            None
          }

        def allowAllReads = copy(readsVdOptOpt = Some(None))
        def writeAllowed = modifiesVdOptOpt.isDefined
      }

      def initEnv: Env = ???  // unused

      def valueFromHeap(recv: Expr, objTpe: ClassType, heapVd: ValDef, fromE: Expr): Expr = {
        val app = MapApply(heapVd.toVariable, recv).copiedFrom(fromE)
        val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
        val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
        Assume(iio, aio).copiedFrom(fromE)
      }

      def checkedRecv(recv: Expr, inSet: Option[Expr], msg: String, result: Expr,
                      fromE: Expr): Expr =
        inSet match {
          case Some(inSet) if checkHeapContracts =>
            Assert(ElementOfSet(recv, inSet).copiedFrom(fromE), Some(msg), result).copiedFrom(fromE)
          case _ =>
            result
        }

      override def transform(e: Expr, env: Env): Expr = e match {
        case ClassConstructor(ct, args) if erasesToHeapRef(ct) =>
          // TODO: Add mechanism to keep freshly allocated objects apart from older ones
          val heapVd = env.expectHeapVd(e.getPos, "allocate heap object")
          val ref = Choose("ref" :: HeapRefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: HeapRefType, ref) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform(_, env))).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform(_, env))).copiedFrom(e)
            val newHeap = MapUpdated(heapVd.toVariable, ref, value).copiedFrom(e)
            let("alloc" :: UnitType(), Assignment(heapVd.toVariable, newHeap).copiedFrom(e)) { _ =>
              ref
            }
          }

        case ClassSelector(recv, field) if erasesToHeapRef(recv.getType) =>
          val heapVd = env.expectHeapVd(e.getPos, "read from heap object")
          val readsDom = env.expectReadsV(e.getPos, "read from heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val sel = ClassSelector(valueFromHeap(recvRef, objTpe, heapVd, e), field).copiedFrom(e)
            checkedRecv(recvRef, readsDom, "read object in reads set", sel, e)
          }

        case FieldAssignment(recv, field, value) if erasesToHeapRef(recv.getType) =>
          if (!env.writeAllowed)
            self.context.reporter.error(e.getPos, "Can't modify heap in read-only context")

          val heapVd = env.expectHeapVd(e.getPos, "write to heap object")
          val modifiesDom = env.expectModifiesV(e.getPos, "write to heap object")
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
              val assgn = Assignment(heapVd.toVariable, newHeap).copiedFrom(e)
              checkedRecv(recvRef, modifiesDom, "modified object in modifies set", assgn, e)
            }
          }

        case IsInstanceOf(recv, tpe) if erasesToHeapRef(tpe) =>
          val heapVd = env.expectHeapVd(e.getPos, "runtime type-check on heap object")
          val readsDom = env.expectReadsV(e.getPos, "runtime type-check heap object")
          val ct = tpe.asInstanceOf[ClassType]

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val app = MapApply(heapVd.toVariable, recvRef).copiedFrom(e)
            val iio = IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)
            checkedRecv(recvRef, readsDom, "runtime type-checked object in reads set", iio, e)
          }

        case e: Old =>
          // Will be translated separately in postconditions
          // TODO(gsps): Add ability to refer back to old state snapshots for any ghost code
          e

        case AsHeapRefSet(objs) =>
          transform(objs, env)

        case RefEq(e1, e2) =>
          // Reference equality is transformed into value equality on references
          Equals(transform(e1, env), transform(e2, env)).copiedFrom(e)

        case ObjectIdentity(recv) =>
          val fieldId = heapRefSort.constructors.head.fields.head.id
          ADTSelector(transform(recv, env), fieldId).copiedFrom(e)

        case HeapGet() =>
          val heap = env.expectHeapVd(e.getPos, "heap snapshot").toVariable
          val readsDom = env.expectReadsV(e.getPos, "heap snapshot")
          readsDom
            .map(readsDom => MapMerge(readsDom, heap, E(dummyHeap.id)()).copiedFrom(e))
            .getOrElse(heap)

        case HeapUnchanged(objs, heap1, heap2) =>
          smartLet("heapBase" :: HeapRefType, transform(heap1, env)) { heapBase =>
            val mm = MapMerge(transform(objs, env), transform(heap2, env), heapBase).setPos(e)
            Equals(mm, heapBase).setPos(e)
          }

        case HeapEval(heap, value) =>
          // FIXME(gsps): Reads and modifies should also be checked within HeapRun.
          val heapVd: ValDef = "heapInEval" :: HeapMapType
          val envInEval = Env(
            readsVdOptOpt = Some(None), // unchecked reads!
            modifiesVdOptOpt = Some(None), // unchecked writes!
            heapVdOpt = Some(heapVd))
          val heap1 = transform(heap, env)
          val value1 = transform(value, envInEval)
          LetVar(heapVd, heap1, value1).setPos(e)

        case fi @ FunctionInvocation(id, targs, vargs) =>
          val targs1 = targs.map(transform(_, env))
          val vargs1 = vargs.map(transform(_, env))

          effectLevel(id) match {
            case None =>
              FunctionInvocation(id, targs1, vargs1).copiedFrom(e)

            case Some(writes) =>
              val heapVd = env.expectHeapVd(e.getPos, "effectful function call")
              val readsDom = env.expectReadsV(e.getPos, "call heap-reading function")
              lazy val modifiesDom = env.expectModifiesV(e.getPos, "call heap-modifying function")

              val call =
                if (readsDom.isEmpty && modifiesDom.isEmpty) {
                  // NOTE: Workaround for the case where both readsDom and modifiesDom is None,
                  //   i.e. all reads and modifications are permitted.
                  FunctionInvocation(id, targs1, Seq(heapVd.toVariable) ++ vargs1).copiedFrom(e)
                } else {
                  // FIXME: Encode the *any reads* and *any writes* cases (when *Dom is None).
                  //   Currently we have no way of signalling this case to the shim.
                  //   We could move from `Set[AnyHeapRef]` to `Option[Set[AnyHeapRef]]`.
                  val extraArgs = Seq(heapVd.toVariable, readsDom.getOrElse(EmptyHeapRefSet)) ++
                    (if (writes) Some(modifiesDom.getOrElse(EmptyHeapRefSet)) else None)
                  FunctionInvocation(shimId(id), targs1, extraArgs ++ vargs1).copiedFrom(e)
                }

              if (writes) {
                // Update the local heap variable and project out the the function result
                val resTpe = T(typeOnlyRefTransformer.transform(fi.tfd.returnType), HeapMapType)
                let("res" :: resTpe, call) { res =>
                  Block(
                    Seq(Assignment(heapVd.toVariable, res._ts2).copiedFrom(e)),
                    res._ts1
                  ).copiedFrom(e)
                }
              } else {
                // Nothing to be done, if the callee only reads from but does not write to the heap
                call
              }
          }

        case _ => super.transform(e, env)
      }

      override def transform(pat: Pattern, env: Env): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if erasesToHeapRef(ct) =>
          val heapVd = env.expectHeapVd(pat.getPos, "class pattern unapply")

          import OptionSort._
          val readsDom = env.expectReadsV(pat.getPos, "call heap-reading unapply")
          val readsDomArg = readsDom match {
            case None => C(none)(HeapRefSetType)()
            case Some(readsDom) => C(some)(HeapRefSetType)(readsDom)
          }

          val newClassPat = ClassPattern(
            None,
            classTypeInHeap(ct),
            subPats.map(transform(_, env))
          ).copiedFrom(pat)
          UnapplyPattern(
            binder.map(transform(_, env)),
            Seq(heapVd.toVariable, readsDomArg),
            unapplyId(ct.id),
            ct.tps.map(transform(_, env)),
            Seq(newClassPat)
          ).copiedFrom(pat)
        case _ =>
          super.transform(pat, env)
      }
    } // << funRefTransformer

    def transformFun(fd: FunDef): Seq[FunDef] = {
      import exprOps._

      val level = effectLevel(fd.id)
      val reads = level.isDefined
      val writes = level.getOrElse(false)

      val heapVdOpt0 = if (reads) Some(freshStateParam()) else None
      val readsDomVdOpt = if (reads) Some(freshRefSetVd("readsDom")) else None
      val modifiesDomVdOpt = if (writes) Some(freshRefSetVd("modifiesDom")) else None
      val newRealParams = fd.params.map(typeOnlyRefTransformer.transform)
      val newParams = heapVdOpt0.toSeq ++ newRealParams
      val newShimParams = Seq(heapVdOpt0, readsDomVdOpt, modifiesDomVdOpt).flatten ++ newRealParams

      val newReturnType = {
        val newReturnType1 = typeOnlyRefTransformer.transform(fd.returnType)
        if (writes) T(newReturnType1, HeapMapType) else newReturnType1
      }

      // Let-bindings to this function's `reads` and `modifies` contract sets
      val readsVdOpt = if (reads) Some(freshRefSetVd("reads")) else None
      val modifiesVdOpt = if (writes) Some(freshRefSetVd("modifies")) else None

      def specEnv(heapVdOpt: Option[ValDef]) =
        funRefTransformer.Env(readsVdOpt.map(Some(_)), modifiesVdOptOpt = None, heapVdOpt)
      def bodyEnv(heapVdOpt: Option[ValDef]) =
        funRefTransformer.Env(readsVdOpt.map(Some(_)), modifiesVdOpt.map(Some(_)), heapVdOpt)

      // Transform postcondition body
      def transformPost(post: Expr, resVd: ValDef, valueVd: ValDef,
                        heapVdOpt0: Option[ValDef], heapVdOpt1: Option[ValDef]): Expr =
      {
        val replaceRes = resVd != valueVd
        // Rewrite the value result variable (used if `resVd` now also contains the heap state)
        val post1 = postMap {
          case v: Variable if replaceRes && v.id == resVd.id =>
            Some(valueVd.toVariable.copiedFrom(v))
          case _ =>
            None
        }(post)
        // Transform postcondition body in post-state (ignoring `old(...)` parts)
        val post2 = funRefTransformer.transform(post1, specEnv(heapVdOpt1))
        // Transform `old(...)` parts of postcondition body in pre-state
        postMap {
          case Old(e) =>
            Some(funRefTransformer.transform(e, specEnv(heapVdOpt0)))
          case _ =>
            None
        }(post2)
      }

      // Unpack specs from the existing function
      val specced = BodyWithSpecs(fd.fullBody)

      // Transform existing specs
      val newSpecsMap: Map[SpecKind, Specification] = specced.specs.map {
        case spec @ Postcondition(lam @ Lambda(Seq(resVd), post)) =>
          val resVd1 = typeOnlyRefTransformer.transform(resVd)
          val (resVd2, post2) = if (writes) {
            val valueVd: ValDef = "resV" :: resVd1.tpe
            val heapVd1: ValDef = "heap1" :: HeapMapType
            val resVd2 = resVd1.copy(tpe = T(resVd1.tpe, HeapMapType))
            val post2 = Let(valueVd, resVd2.toVariable._ts1,
              Let(heapVd1, resVd2.toVariable._ts2,
                transformPost(post, resVd1, valueVd, heapVdOpt0, Some(heapVd1))))
            (resVd2, post2)
          } else {
            (resVd1, transformPost(post, resVd1, resVd1, heapVdOpt0, heapVdOpt0))
          }
          val newSpec = Postcondition(Lambda(Seq(resVd2), post2).copiedFrom(lam))
          (spec.kind, newSpec.setPos(spec.getPos))

        case spec =>
          val newSpec = spec.transform(expr =>
            funRefTransformer.transform(expr, specEnv(heapVdOpt0)))
          (spec.kind, newSpec)
      } .toMap

      // Transform reads spec in a way that doesn't depend on the final `readsVdOpt`
      val newIndependentReadsExpr = specced.specs.collectFirst {
        case spec: ReadsContract =>
          val env = specEnv(heapVdOpt0).allowAllReads
          spec.transform(expr => funRefTransformer.transform(expr, env))
            .asInstanceOf[ReadsContract].expr
      } .getOrElse(EmptyHeapRefSet)

      val newModifiesExpr = newSpecsMap.get(ModifiesKind)
        .map(_.asInstanceOf[ModifiesContract].expr).getOrElse(EmptyHeapRefSet)

      // Translate `reads` and `modifies` into additional precondition
      // TODO(gsps): Support lets and multiple preconditions here.
      val newSpecs: Seq[Specification] = Seq(
        newSpecsMap.get(PostconditionKind),
        newSpecsMap.get(PreconditionKind),
        newSpecsMap.get(MeasureKind),
      ).flatten

      // Transform implementation body (which becomes the inner function, if needed)
      val innerBodyOpt: Option[Expr] = specced.bodyOpt.map { body =>
        if (writes) {
          // Add a locally mutable heap binding
          val heapVd: ValDef = "heap" :: HeapMapType
          val innerNewBody = funRefTransformer.transform(body, bodyEnv(heapVdOpt = Some(heapVd)))
          LetVar(heapVd, heapVdOpt0.get.toVariable,
            E(innerNewBody, heapVd.toVariable))
        } else {
          // Simply transform with pre-state everywhere
          funRefTransformer.transform(body, bodyEnv(heapVdOpt = heapVdOpt0))
        }
      }

      def maybeLetWrap(vdOpt: Option[ValDef], value: => Expr, body: Expr): Expr =
        vdOpt match {
          case Some(vd) => Let(vd, value, body).copiedFrom(body)
          case None => body
        }

      val newTParams = fd.tparams.map(typeOnlyRefTransformer.transform)
      val newFlags = fd.flags.map(typeOnlyRefTransformer.transform)

      /*
        Create a shim for `f` that will always be inlined and looks as follows:

          def f(x: S): T = {
            reads(R)
            modifies(M)
            *body*
          }

        ==>

          def f__shim(heap: Heap,
                      readsDom: Set[HeapRef],
                      modifiesDom: Set[HeapRef],
                      x: S): (T, Heap) = {
            val reads = R
            val modifies = M
            assert(reads ⊆ readsDom)
            assert(modifies ⊆ modifiesDom)
            val heapIn = reads.mapMerge(heap, dummyHeap)
            val (res, heapOut) = f(heapIn, x)
            (res, modifies.mapMerge(heapOut, heap))
          }
      */
      def makeShimFd(): FunDef = {
        val heapArg = MapMerge(
            readsVdOpt.get.toVariable,
            heapVdOpt0.get.toVariable,
            E(dummyHeap.id)()
          ).copiedFrom(fd)

        // NOTE: We omit the position so the inliner can fill it in at the call site.
        val fi = FunctionInvocation(
          fd.id,
          newTParams.map(_.tp),
          Seq(heapVdOpt0.get.toVariable) ++ newRealParams.map(_.toVariable)
        ) //.copiedFrom(fd)

        val body =
          let("res" :: newReturnType, fi) { res =>
            val result = if (writes) {
              Assume(
                unchecked(Equals(
                  res._ts2,
                  MapMerge(
                    modifiesVdOpt.get.toVariable,
                    res._ts2,
                    heapVdOpt0.get.toVariable
                  ).copiedFrom(fd)
                ).copiedFrom(fd)),
                res
              ).copiedFrom(fd)
            } else {
              res
            }
            val fiProjected = fi.copy(args = heapArg +: fi.args.tail).copiedFrom(fi)
            Assume(
              unchecked(
                if (writes) {
                  // resR := f(reads.mapMerge(heap, dummyHeap), x)
                  let("resR" :: newReturnType, fiProjected) { resR =>
                    And(
                      // res._ts1 == resR._ts1
                      Equals(res._ts1, resR._ts1).copiedFrom(fd),
                      // Heap.unchanged(modifies, res._ts2, resR._ts2)
                      Equals(
                        res._ts2,
                        MapMerge(
                          modifiesVdOpt.get.toVariable,
                          resR._ts2,
                          res._ts2
                        ).copiedFrom(fd)
                      ).copiedFrom(fd)
                    ).copiedFrom(fd)
                  }
                } else {
                  Equals(res, fiProjected).copiedFrom(fd)
                }
              ),
              result
            ).copiedFrom(fd)
          }

        val bodyWithContractChecks =
          if (checkHeapContracts) {
            val niceFdName = fd.id match {
              case si: SymbolIdentifier => si.symbol.name
              case id => id.name
            }

            // NOTE: Leaving out position on conditions, so inliner will fill them in at call site.
            val check1 =
              if (writes) {
                val cond1 = SubsetOf(
                  modifiesVdOpt.get.toVariable,
                  modifiesDomVdOpt.get.toVariable
                ) //.copiedFrom(fd)
                Assert(cond1, Some(s"modifies of $niceFdName"), body).copiedFrom(fd)
              } else {
                body
              }

            val cond2 = SubsetOf(
              readsVdOpt.get.toVariable,
              readsDomVdOpt.get.toVariable
            ) //.copiedFrom(fd)
            Assert(cond2, Some(s"reads of $niceFdName"), check1).copiedFrom(fd)
          } else {
            body
          }

        // Wrap in reads and modifies expression bindings
        val fullBody =
          maybeLetWrap(
            readsVdOpt,
            unchecked(newIndependentReadsExpr),
            maybeLetWrap(
              modifiesVdOpt,
              unchecked(newModifiesExpr),
              bodyWithContractChecks))

        freshenSignature(new FunDef(
          shimId(fd.id),
          newTParams,
          newShimParams,
          newReturnType,
          freshenLocals(fullBody),
          (newFlags.filter(flag => flag != Inline && flag != Opaque && flag != Extern) ++
            Seq(Synthetic, DropVCs, InlineOnce)).distinct
        ).copiedFrom(fd))
      }

      def makeInnerFd(bodyOpt: Option[Expr]): FunDef = {
        // Reconstruct body and wrap in reads expression binding (modifies binding is inside)
        val fullBody =
          maybeLetWrap(
            readsVdOpt,
            unchecked(newIndependentReadsExpr),
            specced.withBody(bodyOpt, newReturnType).copy(specs = newSpecs).reconstructed)

        new FunDef(
          fd.id,
          newTParams,
          newParams,
          newReturnType,
          fullBody,
          newFlags
        ).copiedFrom(fd)
      }

      if (reads) {
        // We duplicate the reads clause to compensate for it being unchecked when first bound.
        // This solves an issue with bootstrapping reads checks: The reads clause should be subject
        // to its own restrictions (i.e., it must not read outside the reads clause), but we cannot
        // refer to `readsVdOpt` while defining it. Instead, we first translate the reads clause
        // without checks in inner body and insert an additional, checked copy here.
        val innerBody1 = innerBodyOpt.getOrElse(NoTree(newReturnType).copiedFrom(fd))
        val innerBody2 = newSpecsMap.get(ReadsKind) match {
          case Some(newReadsSpec) =>
            // TODO: Even though this copy of the reads expressions is pure and unused, the VC
            //   generator will gather its assertions and add them to the context, slowing things
            //   down. We could annotate this expression accordingly and shave off a few seconds
            //   lost in hard VCs.
            val newReadsExpr = newReadsSpec.asInstanceOf[ReadsContract].expr
            Block(Seq(newReadsExpr), innerBody1).copiedFrom(innerBody1)
          case None =>
            innerBody1
        }

        // We also ensure that the reads set subsumes modifies set
        val innerBody3 = if (writes && checkHeapContracts) {
          val cond = SubsetOf(
            modifiesVdOpt.get.toVariable,
            readsVdOpt.get.toVariable
          ).copiedFrom(fd)
          Assert(cond, Some("reads subsumes modifies clause"), innerBody2).copiedFrom(fd)
        } else {
          innerBody2
        }

        // Wrap in modifies expression binding
        val innerBody4 = maybeLetWrap(
          modifiesVdOpt,
          unchecked(newModifiesExpr),
          innerBody3)

        val innerFd = makeInnerFd(Some(innerBody4))
        val shimFd = makeShimFd()
        Seq(shimFd, innerFd)

      } else {
        // Pure functions are merely ref-transformed.
        Seq(makeInnerFd(innerBodyOpt))
      }
    }
  }
}
