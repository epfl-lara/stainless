/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

object optCheckHeapContracts extends inox.FlagOptionDef("check-heap-contracts", true)

// false = counter, true = set
object optAllocImpl extends inox.OptionDef[Boolean] {
  val name = "alloc-impl"
  def default = true
  def parser = {
    case "counter" => Some(false)
    case "set" => Some(true)
    case _ => None
  }
  def usageRhs = "counter|set"
  override def formatDefault = "set"
}

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
    // We filter out the definitions related to AnyHeapRef since they are only needed for inferring
    // which types live on the heap.
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.filterNot(fd => hasFlag(fd, "refEq")).toSeq)
      .withClasses(symbols.classes.values.filterNot(cd => hasFlag(cd, "anyHeapRef")).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    super.extractSymbols(tctx, newSymbols)
      .withSorts(Seq(heapRefSort) ++ OptionSort.sorts(newSymbols))
      .withFunctions(Seq(dummyHeap) ++ OptionSort.functions(newSymbols))
      // .withSorts(Seq(heapRefSort, heapSort) ++ OptionSort.sorts(newSymbols))
      // .withFunctions(heapFunctions ++ OptionSort.functions(newSymbols))
  }

  override protected def extractFunction(tctx: TransformerContext, fd: FunDef): FunctionResult =
    tctx.transformFun(fd)

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

/*
trait SyntheticHeapFunctions { self =>
  val s: Trees
  val t: s.trees

  import t._
  import dsl._

  protected lazy val heapReadId: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef.read")
  protected lazy val heapModifyId: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef.modify")

  protected def heapFunctions: Seq[FunDef] = {
    val readFd = mkFunDef(heapReadId, Unchecked, Synthetic, Inline)() { _ =>
      (Seq("heap" :: HeapType, "x" :: HeapRefType), AnyType(), {
        case Seq(heap, x) =>
          Require(
            heap.select(heapReadableId).contains(x),
            MapApply(heap.select(heapMapId), x)
          )
      })
    }
    val modifyFd = mkFunDef(heapModifyId, Unchecked, Synthetic, Inline)() { _ =>
      (Seq("heap" :: HeapType, "x" :: HeapRefType, "v" :: AnyType()), UnitType(), {
        case Seq(heap, x) =>
          Require(
            heap.select(heapModifiableId).contains(x),
            heapWithMap(heap, MapUpdated(heap.select(heapMapId), x, v))
          )
      })
    }
    Seq(readFd, modifyFd)
  }

  protected def heapWithMap(oldHeap: Expr, newMap: Expr): Expr =
    C(heapCons)(
      newMap,
      oldHeap.select(heapReadableId),
      oldHeap.select(heapModifiableId)
    )
}
*/

trait RefTransform extends oo.CachingPhase with utils.SyntheticSorts /*with SyntheticHeapFunctions*/ { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._
  import context.reporter.error

  lazy val checkHeapContracts = self.context.options.findOptionOrDefault(optCheckHeapContracts)

  /* Heap encoding */

  protected lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)
  protected lazy val shimId = new utils.ConcurrentCached[Identifier, Identifier](
    id => FreshIdentifier(s"${id.name}__shim")
  )

  // Switch between the two available implementations of allocation
  lazy val allocUsingSets = context.options.findOptionOrDefault(optAllocImpl)

  /* The transformer */

  protected type TransformerContext <: RefTransformContext

  trait RefTransformContext { context: TransformerContext =>
    implicit val symbols: s.Symbols

    lazy val HeapRefSetType: Type = SetType(HeapRefType)
    lazy val EmptyHeapRefSet: Expr = FiniteSet(Seq.empty, HeapRefType)

    // The type of the allocation instrumentation
    lazy val AllocInstrumType: Type =
      if (allocUsingSets) HeapRefSetType
      else IntegerType()

    lazy val dummyHeapVd = "dummyHeap" :: HeapType
    lazy val dummyHeapRefSetVd = "dummyHeapRefSet" :: HeapRefSetType
    lazy val dummyAllocVd = "dummyAlloc" :: IntegerType()

    // This caches whether types live in the heap or not
    lazy val isHeapType = new utils.ConcurrentCached[Type, Boolean](_isHeapType(_))

    protected lazy val effectLevel = new utils.ConcurrentCached[Identifier, exprOps.EffectLevel]({
      id => exprOps.getEffectLevel(symbols.getFunction(id))
    })

    private def _isHeapType(tpe: Type): Boolean = tpe match {
      case AnyHeapRef() => true
      // We lookup the parents through the cache so that the hierarchy is traversed at most once
      case ct: ClassType => ct.tcd.parents.exists(a => isHeapType(a.toType))
      case _ => false
    }

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }

    def unchecked(expr: Expr): Expr = Annotated(expr, Seq(Unchecked)).copiedFrom(expr)

    def classTypeInHeap(ct: ClassType): ClassType =
      ClassType(ct.id, ct.tps.map(typeOnlyRefTransformer.transform)).copiedFrom(ct)

    def makeClassUnapply(cd: ClassDef): Option[FunDef] = {
      if (!isHeapType(cd.typed.toType))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        // NOTE: Here we allow `readsDom` to be `None` to allow any access and `Some(dom)`
        //   to restrict reads to `dom`.
        (
          Seq("heap" :: HeapType, "readsDom" :: T(option)(HeapRefSetType), "x" :: HeapRefType),
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
    abstract class RefTransformer extends oo.DefinitionTransformer {
      val s: self.s.type = self.s
      val t: self.s.type = self.s

      override def transform(tpe: Type, env: Env): Type = tpe match {
        case ct: ClassType if isHeapType(ct) =>
          HeapRefType
        // case FunctionType(_, _) =>
        //   val FunctionType(from, to) = super.transform(tpe, env)
        //   FunctionType(HeapType +: from, T(to, HeapType))
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
      private lazy val dummyHeapVd: ValDef = "dummyHeap" :: HeapRefSetType

      case class Env(
        readsVdOptOpt: Option[Option[ValDef]],
        modifiesVdOptOpt: Option[Option[ValDef]],
        heapVdOpt: Option[ValDef],
        allocVdOpt: Option[ValDef],
        allocAllowed: Boolean
      ) {
        def expectHeapV(pos: Position, usage: String): Variable =
          heapVdOpt.map(_.toVariable) getOrElse {
            error(pos, s"Cannot use heap-accessing construct ($usage) here")
            dummyHeapVd.toVariable
          }

        def expectReadsV(pos: Position, usage: String): Option[Variable] =
          readsVdOptOpt.map(_.map(_.toVariable)) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a reads clause")
            None
          }

        def expectModifiesV(pos: Position, usage: String): Option[Variable] =
          modifiesVdOptOpt.map(_.map(_.toVariable)) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a modifies clause")
            None
          }

        def expectAllocV(pos: Position, usage: String, alloc: Boolean = false): Variable =
          if (alloc && !allocAllowed) {
            error(pos, s"Cannot use allocating construct ($usage) here")
            dummyAllocVd.toVariable
          } else allocVdOpt.map(_.toVariable) getOrElse {
            error(pos, s"Cannot access allocation information ($usage) here")
            dummyAllocVd.toVariable
          }

        def allowAllReads = copy(readsVdOptOpt = Some(None))
        def writeAllowed = modifiesVdOptOpt.isDefined
      }

      def initEnv: Env = ???  // unused

      def valueFromHeap(recv: Expr, objTpe: ClassType, heapV: Variable, fromE: Expr): Expr = {
        val app = MapApply(heapV, recv).copiedFrom(fromE)
        val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
        val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
        Assume(iio, aio).copiedFrom(fromE)
      }

      def checkedRecv(recv: Expr, inSet: Option[Expr], allocAllowed: Boolean, msg: String, result: Expr,
                      fromE: Expr): Expr =
        inSet match {
          case Some(inSet) if checkHeapContracts =>
            val isInSet = ElementOfSet(recv, inSet).copiedFrom(fromE)
            val cond =
              if (allocAllowed) {
                Implies(
                  Old(Allocated(recv).copiedFrom(fromE)).copiedFrom(fromE),
                  isInSet
                ).copiedFrom(fromE)
              } else isInSet
            Assert(cond, Some(msg), result).copiedFrom(fromE)
          case _ =>
            result
        }
        
      def allocated(allocV: Variable, ref: Expr, fromE: Expr): Expr =
        if (allocUsingSets) ElementOfSet(ref, allocV).copiedFrom(fromE)
        else LessThan(getHeapRefId(ref), allocV)

      def notAllocated(allocV: Variable, ref: Expr, fromE: Expr): Expr =
        if (allocUsingSets) Not(ElementOfSet(ref, allocV).copiedFrom(fromE)).copiedFrom(fromE)
        else GreaterEquals(getHeapRefId(ref), allocV).copiedFrom(fromE)

      def assumeAlloc(allocVdOpt: Option[ValDef], ref: Expr)(e: Expr): Expr =
        allocVdOpt map { allocVd =>
          Assume(allocated(allocVd.toVariable, ref, e), e).copiedFrom(e)
        } getOrElse e

      def transformReturnType(returnType: Type, writes: Boolean, allocs: Boolean): Type = {
        var retTypes = Seq(typeOnlyRefTransformer.transform(returnType)) ++
          (if (writes) Seq(HeapType) else Seq()) ++
          (if (allocs) Seq(AllocInstrumType) else Seq())
        tupleTypeWrap(retTypes)
      }

      override def transform(e: Expr, env: Env): Expr = e match {
        // Reference equality is transformed into value equality on references
        case RefEq(e1, e2) =>
          Equals(transform(e1, env), transform(e2, env)).copiedFrom(e)

        case ClassConstructor(ct, args) if isHeapType(ct) =>
          // To allocate, we need both the allocated set and the heap
          val allocV = env.expectAllocV(e.getPos, "allocate heap object", alloc = true)
          val heapV = env.expectHeapV(e.getPos, "allocate heap object")

          val freshRef =
            if (allocUsingSets) {
              Assume(
                !forall("ref" :: HeapRefType) { ref =>
                  allocated(allocV, ref, e)
                },
                choose("ref" :: HeapRefType) { ref =>
                  !allocV.contains(ref)
                }.copiedFrom(e)
              )
            } else {
              createHeapRef(allocV)
            }

          let("ref" :: HeapRefType, freshRef) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform(_, env))).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform(_, env))).copiedFrom(e)
            val newHeap = MapUpdated(heapV, ref, value).copiedFrom(e)
            val newAllocated = 
              if (allocUsingSets) SetAdd(allocV, ref).copiedFrom(e)
              else Plus(allocV, IntegerLiteral(1)).copiedFrom(e)
            Block(
              Seq(
                Assignment(allocV, newAllocated).copiedFrom(e),
                Assignment(heapV, newHeap).copiedFrom(e)
              ),
              ref
            )
          }

        case cs @ ClassSelector(recv, field) if isHeapType(recv.getType) =>
          val heapV = env.expectHeapV(e.getPos, "read from heap object")
          val readsDom = env.expectReadsV(e.getPos, "read from heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val sel = ClassSelector(valueFromHeap(recvRef, objTpe, heapV, e), field).copiedFrom(e)
            val checkedAlloc = if (isHeapType(cs.getType) && env.allocVdOpt.isDefined) {
              let("res" :: HeapRefType, sel) { res =>
                assumeAlloc(env.allocVdOpt, res)(res)
              }
            } else sel
            checkedRecv(recvRef, readsDom, env.allocAllowed, "read object in reads set", checkedAlloc, e)
          }

        case FieldAssignment(recv, field, value) if isHeapType(recv.getType) =>
          if (!env.writeAllowed)
            error(e.getPos, "Can't modify heap in read-only context")

          val heapV = env.expectHeapV(e.getPos, "write to heap object")
          val modifiesDom = env.expectModifiesV(e.getPos, "write to heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val oldObj = valueFromHeap(recvRef, objTpe, heapV, e)
            let("oldObj" :: objTpe, oldObj) { oldObj =>
              val newCt = objTpe.asInstanceOf[ClassType]
              val newArgs = newCt.tcd.fields.map {
                case vd if vd.id == field => transform(value, env)
                case vd => ClassSelector(oldObj, vd.id).copiedFrom(e)
              }
              val newObj = ClassConstructor(newCt, newArgs).copiedFrom(e)
              val newHeap = MapUpdated(heapV, recvRef, newObj).copiedFrom(e)
              val assgn = Assignment(heapV, newHeap).copiedFrom(e)
              checkedRecv(recvRef, modifiesDom, env.allocAllowed, "modified object in modifies set", assgn, e)
            }
          }

        case IsInstanceOf(recv, tpe) if isHeapType(tpe) =>
          val heapV = env.expectHeapV(e.getPos, "runtime type-check on heap object")
          val readsDom = env.expectReadsV(e.getPos, "runtime type-check heap object")
          val ct = tpe.asInstanceOf[ClassType]

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val app = MapApply(heapV, recvRef).copiedFrom(e)
            val iio = IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)
            checkedRecv(recvRef, readsDom, env.allocAllowed, "runtime type-checked object in reads set", iio, e)
          }

        case ObjectIdentity(recv) =>
          val fieldId = heapRefSort.constructors.head.fields.head.id
          ADTSelector(transform(recv, env), fieldId).copiedFrom(e)

        case fi @ FunctionInvocation(id, targs, vargs) =>
          val targs1 = targs.map(transform(_, env))
          val vargs1 = vargs.map(transform(_, env))

          val level = effectLevel(id)
          val writes = level.getOrElse(false)
          val allocs = exprOps.allocates(symbols.getFunction(id))

          // Incrementally build the arguments and the block after the function invocation
          var newArgs = vargs1
          var block: Seq[Expr] = Seq()
          val resTpe = transformReturnType(fi.tfd.returnType, writes, allocs)       

          // Expressions to access the instrumented parts from the returned tuple
          lazy val resValDef = "res" :: resTpe
          lazy val retResult = TupleSelect(resValDef.toVariable, 1).copiedFrom(e)
          lazy val retHeap = TupleSelect(resValDef.toVariable, 2).copiedFrom(e)
          lazy val retAlloc = TupleSelect(resValDef.toVariable, if (writes) 3 else 2).copiedFrom(e)

          // If the function allocates, we thread the allocation state through the call
          if (allocs) {
            val allocV = env.expectAllocV(e.getPos, "calling a function that allocates", alloc = true)
            newArgs +:= allocV
            block :+= Assignment(allocV, retAlloc).copiedFrom(e)
          }

          effectLevel(id) match {
            case Some(writes) =>
              val heapV = env.expectHeapV(e.getPos, "effectful function call")
              val readsDom = env.expectReadsV(e.getPos, "call heap-reading function")
              lazy val modifiesDom = env.expectModifiesV(e.getPos, "call heap-modifying function")

              // We add the extra arguments to the call
              if (writes)
                newArgs +:= modifiesDom.getOrElse(EmptyHeapRefSet)
              newArgs ++:= Seq(heapV, readsDom.getOrElse(EmptyHeapRefSet))

              // If the function writes to the heap, we also extract the modified heap
              if (writes)
                block :+= Assignment(heapV, retHeap).copiedFrom(e)
            
            case _ =>
          }

          // We ad the new arguments to the call
          val call = FunctionInvocation(shimId(id), targs1, newArgs).copiedFrom(e)

          // If the function doesn't return additional data, we don't need to unwrap the return value
          if (!(allocs || writes)) call
          else {
            // Otherwise we let-bind the result and add the instrumentation block
            let(resValDef, call) { res =>
              Block(
                block,
                retResult
              ).copiedFrom(e)
            }
          }

        case e: Old =>
          // Will be translated separately in postconditions
          // TODO(gsps): Add ability to refer back to old state snapshots for any ghost code
          e

        case Allocated(ref) =>
          val allocV = env.expectAllocV(e.getPos, "checking allocation")
          allocated(allocV, transform(ref, env), e)

        case _ => super.transform(e, env)
      }

      override def transform(pat: Pattern, env: Env): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if isHeapType(ct) =>
          val heapV = env.expectHeapV(pat.getPos, "class pattern unapply")

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
            Seq(heapV, readsDomArg),
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
      val allocs = exprOps.allocates(symbols.getFunction(fd.id))

      val heapVdOpt0 = if (reads) Some("heap0" :: HeapType) else None
      val heapVdOpt1 = if (writes) Some("heap1" :: HeapType) else None
      val allocVdOpt0 = if (allocs) Some("alloc0" :: AllocInstrumType) else None
      val allocVdOpt1 = if (allocs) Some("alloc1" :: AllocInstrumType) else None
      val readsDomVdOpt = if (reads) Some("readsDom" :: HeapRefSetType) else None
      val modifiesDomVdOpt = if (writes) Some("modifiesDom" :: HeapRefSetType) else None
      val newRealParams = fd.params.map(typeOnlyRefTransformer.transform)
      val newReturnType = funRefTransformer.transformReturnType(fd.returnType, writes, allocs)
      val newParams = Seq(heapVdOpt0, allocVdOpt0).flatten ++ newRealParams
      val newShimParams = Seq(heapVdOpt0, readsDomVdOpt, modifiesDomVdOpt, allocVdOpt0).flatten ++ newRealParams

      // Let-bindings to this function's `reads` and `modifies` contract sets
      val readsVdOpt = if (reads) Some("reads" :: HeapRefSetType) else None
      val modifiesVdOpt = if (writes) Some("modifies" :: HeapRefSetType) else None

      def specEnv(heapVdOpt: Option[ValDef], allocVdOpt: Option[ValDef], readsVdOpt: Option[ValDef] = readsVdOpt) =
        funRefTransformer.Env(readsVdOpt.map(Some(_)), modifiesVdOptOpt = None, heapVdOpt, allocVdOpt, allocAllowed = false)
      def bodyEnv(heapVdOpt: Option[ValDef], allocVdOpt: Option[ValDef]) =
        funRefTransformer.Env(readsVdOpt.map(Some(_)), modifiesVdOpt.map(Some(_)), heapVdOpt, allocVdOpt, allocVdOpt.isDefined)

      // Transform postcondition body
      def transformPost(post: Expr, resVd: ValDef, valueVd: ValDef): Expr = {
        // Transform postcondition body in post-state (ignoring `old(...)` parts)
        val post1 = funRefTransformer.transform(post, specEnv(heapVdOpt1, allocVdOpt1))

        // Rewrite the value result variable (used if `resVd` now also contains the heap state)
        val replaceRes = resVd != valueVd
        val post2 = postMap {
          case v: Variable if replaceRes && v.id == resVd.id =>
            Some(valueVd.toVariable.copiedFrom(v))
          case _ =>
            None
        } (post1)

        // Transform `old(...)` and `fresh(...)`
        postMap {
          case o @ Old(e) =>
            if (!writes)
              error(o.getPos, "Can't use 'old' in a function that does not modify the heap")

            Some(funRefTransformer.transform(e, specEnv(heapVdOpt0, allocVdOpt0)))

          case f @ Fresh(ref) =>
            if (!allocs)
              error(f.getPos, "Can't use 'fresh' in a non-allocating function")

            val notAlloc0 = funRefTransformer.notAllocated(allocVdOpt0.getOrElse(dummyAllocVd).toVariable, ref, f)
            val alloc1 = funRefTransformer.allocated(allocVdOpt1.getOrElse(dummyAllocVd).toVariable, ref, f)
            Some(And(Seq(notAlloc0, alloc1)).copiedFrom(f))
          
          case _ =>
            None
        } (post2)
      }

      // Unpack specs from the existing function
      val specced = BodyWithSpecs(fd.fullBody)

      // Transform existing specs
      val newSpecsMap: Map[SpecKind, Specification] = specced.specs.map {
        case spec @ Postcondition(lam @ Lambda(Seq(resVd), post)) =>
          val (resVd1, post1) = if (writes || allocs) {
            val valueVd: ValDef = "resV" :: typeOnlyRefTransformer.transform(resVd.tpe)
            val resVd1 = resVd.copy(tpe = newReturnType)
            var newPost = transformPost(post, resVd, valueVd)
            if (allocs)
              newPost = Let(allocVdOpt1.get, TupleSelect(resVd1.toVariable, if (writes) 3 else 2), newPost)
            if (writes)
              newPost = Let(heapVdOpt1.get, resVd1.toVariable._2, newPost)
            newPost = Let(valueVd, resVd1.toVariable._1, newPost)
            (resVd1, newPost)
          } else {
            (resVd, transformPost(post, resVd, resVd))
          }
          val newSpec = Postcondition(Lambda(Seq(resVd1), post1).copiedFrom(lam))
          (spec.kind, newSpec.setPos(spec.getPos))

        case spec =>
          (spec.kind, spec.map(expr => funRefTransformer.transform(expr, specEnv(heapVdOpt0, allocVdOpt0))))
      }.toMap

      // Transform reads spec in a way that doesn't depend on the final `readsVdOpt`
      val newIndependentReadsExpr = specced.specs.collectFirst {
        case spec: ReadsContract =>
          val env = specEnv(heapVdOpt0, allocVdOpt0).allowAllReads
          spec.map(expr => funRefTransformer.transform(expr, env)).expr
      } .getOrElse(EmptyHeapRefSet)

      // Translate `reads` and `modifies` into additional precondition
      val newSpecs: Seq[Specification] = Seq(
        newSpecsMap.get(PostconditionKind),
        newSpecsMap.get(PreconditionKind),
        newSpecsMap.get(MeasureKind),
      ).flatten

      val innerBodyOpt: Option[Expr] = specced.bodyOpt.map { body =>
        val heapVdOpt = if (writes) Some("heap" :: HeapType) else heapVdOpt0
        val allocVdOpt = if (allocs) Some("alloc" :: AllocInstrumType) else None

        // We replace the `old` statements in the body
        val withoutOld = postMap {
          case o @ Old(e) =>
            Some(funRefTransformer.transform(e, bodyEnv(heapVdOpt0, allocVdOpt0)))
          case _ =>
            None
        } (funRefTransformer.transform(body, bodyEnv(heapVdOpt, allocVdOpt)))

        // We build the resulting expression and the enclosing var definitions
        var results = Seq(withoutOld)
        var varDefs: Seq[(ValDef, Expr)] = Seq()

        if (writes) {
          results :+= heapVdOpt.get.toVariable
          varDefs :+= (heapVdOpt.get, heapVdOpt0.get.toVariable)
        }

        if (allocs) {
          results :+= allocVdOpt.get.toVariable
          varDefs :+= (allocVdOpt.get, allocVdOpt0.get.toVariable)
        }

        // We wrap the instrumented state in a tuple and add var definitions
        val tuple = tupleWrap(results)
        val withVars = varDefs.foldRight(tuple) {
          case ((vd, value), acc) => LetVar(vd, value, acc)
        }

        // We add assumptions that all the parameters that live in the heap are allocated
        val allocVds = if (allocs) newParams.filter(_.tpe == HeapRefType) else Seq()
        allocVds.foldRight(withVars) {
          case (vd, acc) => funRefTransformer.assumeAlloc(allocVdOpt0, vd.toVariable)(acc)
        }
      }

      def maybeLetWrap(vdOpt: Option[ValDef], value: => Expr, body: Expr): Expr =
        vdOpt match {
          case Some(vd) => Let(vd, unchecked(value), body).copiedFrom(body)
          case None => body
        }

      val newTParams = fd.tparams.map(typeOnlyRefTransformer.transform)
      val newFlags = fd.flags.map(typeOnlyRefTransformer.transform).filterNot(_.name == "allocates")

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
          Seq(heapArg) ++ newRealParams.map(_.toVariable)
        ) //.copiedFrom(fd)

        val body =
          if (writes) {
            let("res" :: newReturnType, fi) { res =>
              var modifiedRefs: Expr = modifiesVdOpt.get.toVariable
              if (allocs) {
                if (allocUsingSets) modifiedRefs = modifiedRefs ++ (res._3 -- allocVdOpt0.get.toVariable)
                // TODO: quantifiers inside choose aren't allowed -> find another way for the counter encoding
                // else {
                //   modifiedRefs = modifiedRefs ++ choose("set" :: HeapRefSetType) { set =>
                //     forall("ref" :: HeapRefType) { ref =>
                //       val refId = getHeapRefId(ref)
                //       val inSet = ElementOfSet(ref, set)
                //       val inRange = And(Seq(
                //         GreaterEquals(refId, allocVdOpt0.get.toVariable),
                //         LessThan(refId, res._3)
                //       ))
                //       Equals(inSet, inRange)
                //     }
                //   }
                // }
              }

              val allocRes = if (allocs) {
                val allocIncreased =
                  if (allocUsingSets) SubsetOf(allocVdOpt0.get.toVariable, res._3)
                  else LessEquals(allocVdOpt0.get.toVariable, res._3)
                Some(Assume(allocIncreased, res._3))
              } else None

              Tuple(
                Seq(
                  res._1,
                  MapMerge(
                    modifiedRefs,
                    res._2,
                    heapVdOpt0.get.toVariable
                  ).copiedFrom(fd)
                ) ++ allocRes.toSeq
              )
            }
          } else {
            fi
          }

        val bodyWithContractChecks =
          if (checkHeapContracts) {
            // NOTE: Leaving out position on conditions, so inliner will fill them in at call site.
            val check1 =
              if (writes) {
                val cond1 = SubsetOf(
                  modifiesVdOpt.get.toVariable,
                  modifiesDomVdOpt.get.toVariable
                ) //.copiedFrom(fd)
                Assert(cond1, Some("modifies clause"), body).copiedFrom(fd)
              } else {
                body
              }

            val cond2 = SubsetOf(
              readsVdOpt.get.toVariable,
              readsDomVdOpt.get.toVariable
            ) //.copiedFrom(fd)
            Assert(cond2, Some("reads clause"), check1).copiedFrom(fd)
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
              unchecked(newSpecsMap.get(ModifiesKind).map(_.expr).getOrElse(EmptyHeapRefSet)),
              bodyWithContractChecks))

        freshenSignature(new FunDef(
          shimId(fd.id),
          newTParams,
          newShimParams,
          newReturnType,
          freshenLocals(fullBody),
          (newFlags ++ Seq(Synthetic, Unchecked, InlineOnce)).distinct
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
            Block(Seq(newReadsSpec.expr), innerBody1).copiedFrom(innerBody1)
          case None =>
            innerBody1
        }

        // We also ensure that the reads set subsumes modifies set
        val innerBody3 = if (writes) {
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
          unchecked(newSpecsMap.get(ModifiesKind).map(_.expr).getOrElse(EmptyHeapRefSet)),
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
