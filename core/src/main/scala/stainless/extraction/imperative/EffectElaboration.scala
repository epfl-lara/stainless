/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

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
      .withFunctions(symbols.functions.values.filterNot(fd => hasFlag(fd, "refEq")).toSeq)
      .withClasses(symbols.classes.values.filterNot(cd => hasFlag(cd, "anyHeapRef")).toSeq)
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

    lazy val EmptyHeap = FiniteMap(Seq(), UnitLiteral(), HeapRefType, AnyType())

    // This caches whether types live in the heap or not
    lazy val livesInHeap = new utils.ConcurrentCached[Type, Boolean](isHeapType(_))

    // This caches the effect level for the function definitions
    lazy val effectLevel = new utils.ConcurrentCached[Identifier, exprOps.EffectLevel]({ id =>
      exprOps.getEffectLevel(symbols.getFunction(id))
    })

    private def isHeapType(tpe: Type): Boolean = tpe match {
      case AnyHeapRef() => true
      // We lookup the parents through the cache so that the hierarchy is traversed at most once
      case ct: ClassType => ct.tcd.parents.exists(a => livesInHeap(a.toType))
      case _ => false
    }

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
      import self.context.reporter.error

      val HeapRefSet: Type = SetType(HeapRefType)
      val EmptyHeapRefSet: Expr = FiniteSet(Seq.empty, HeapRefType)

      private lazy val dummyHeapVd: ValDef = "dummyHeap" :: HeapRefSet
      private lazy val dummyAllocatedVd: ValDef = "dummyAllocated" :: HeapRefSet
      private val readSetVd: ValDef = "readSet" :: HeapRefSet
      private val writeSetVd: ValDef = "writeSet" :: HeapRefSet

      case class Env(
        writeAllowed: Boolean,
        allocAllowed: Boolean,
        updateSets: Boolean,
        heapVdOpt: Option[ValDef],
        allocVdOpt: Option[ValDef]
      ) {
        def expectHeapVd(pos: Position, usage: String) =
          heapVdOpt getOrElse {
            error(pos, s"Cannot use effectful construct ($usage) here")
            dummyHeapVd
          }
        def expectAllocVdOpt(pos: Position, usage: String) =
          allocVdOpt getOrElse {
            error(pos, s"Cannot use allocating construct ($usage) here")
            dummyAllocatedVd
          }
      }
      def initEnv: Env = ???  // unused
      def specEnv(heapVdOpt: Option[ValDef], allocVdOpt: Option[ValDef]) =
        Env(writeAllowed = false, allocAllowed = false, updateSets = false, heapVdOpt, allocVdOpt)
      def bodyEnv(writeAllowed: Boolean, heapVdOpt: Option[ValDef], allocVdOpt: Option[ValDef]) =
        Env(writeAllowed, allocAllowed = true, updateSets = true, heapVdOpt, allocVdOpt)

      /**
       * Given an optional set of read expressions, and an input heap, projects the heap along
       * the read variables. The projection is conservative so that if no read clause is given,
       * everything is assumed to be read.
       */
      def projectHeap(subst: Map[ValDef, Expr], reads: Option[Expr], heapVd: ValDef): Expr =
        reads
          .map(r => MapMerge(transform(replaceFromSymbols(subst, r), specEnv(Some(heapVd), None)),
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
          .map(m => MapMerge(transform(replaceFromSymbols(subst, m), specEnv(Some(inputHeapVd), None)),
                             outputHeap, inputHeapVd.toVariable))
          .getOrElse(outputHeap)

      def assumeAlloc(allocVdOpt: Option[ValDef], ref: Expr)(e: Expr): Expr = allocVdOpt match {
        case Some(allocatedVd) =>
          val isAllocated = ElementOfSet(ref, allocatedVd.toVariable).copiedFrom(e)
          Assume(isAllocated, e).copiedFrom(e)
        case None => e
      }

      def valueFromHeap(
        recv: Expr,
        objTpe: ClassType,
        heapVd: ValDef,
        allocVdOpt: Option[ValDef],
        fromE: Expr
      ): Expr = {
        val app = MapApply(heapVd.toVariable, recv).copiedFrom(fromE)
        val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
        val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
        assumeAlloc(allocVdOpt, recv) {
          Assume(iio, aio).copiedFrom(fromE)
        }
      }

      def transformReturnType(returnType: Type, writes: Boolean, allocs: Boolean): Type = {
        var retTypes = Seq(typeOnlyRefTransformer.transform(returnType))
        if (writes)
          retTypes :+= HeapType
        if (allocs)
          retTypes :+= HeapRefSet
        tupleTypeWrap(retTypes)
      }

      override def transform(e: Expr, env: Env): Expr = e match {
        // Reference equality is transformed into value equality on references
        case RefEq(e1, e2) =>
          Equals(transform(e1, env), transform(e2, env))

        case ClassConstructor(ct, args) if livesInHeap(ct) =>
          if (!env.allocAllowed)
            error(e.getPos, "Can't allocate on the heap in this context")

          // To allocate, we need both the allocated set and the heap
          val allocatedVd = env.expectAllocVdOpt(e.getPos, "allocate heap object")
          val heapVd = env.expectHeapVd(e.getPos, "allocate heap object")
          val freshRef = choose("ref" :: HeapRefType) { ref =>
            !allocatedVd.toVariable.contains(ref)
          }.copiedFrom(e)

          let("ref" :: HeapRefType, freshRef) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform(_, env))).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform(_, env))).copiedFrom(e)
            val newAllocated = SetAdd(allocatedVd.toVariable, ref).copiedFrom(e)
            val newHeap = MapUpdated(heapVd.toVariable, ref, value).copiedFrom(e)
            Block(
              Seq(
                Assignment(allocatedVd.toVariable, newAllocated).copiedFrom(e),
                Assignment(heapVd.toVariable, newHeap).copiedFrom(e)
              ),
              ref
            )
          }

        case ClassSelector(recv, field) if livesInHeap(recv.getType) =>
          val heapVd = env.expectHeapVd(e.getPos, "read from heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            ClassSelector(valueFromHeap(recvRef, objTpe, heapVd, env.allocVdOpt, e), field).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) if livesInHeap(recv.getType) =>
          if (!env.writeAllowed)
            error(e.getPos, "Can't modify heap in this context")

          val heapVd = env.expectHeapVd(e.getPos, "write to heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val oldObj = valueFromHeap(recvRef, objTpe, heapVd, env.allocVdOpt, e)
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
          val newRecv = transform(recv, env)
          val app = MapApply(heapVd.toVariable, newRecv).copiedFrom(e)
          assumeAlloc(env.allocVdOpt, newRecv) {
            IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)
          }

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

          if (allocs) {
            if (!env.allocAllowed)
              error(e.getPos, "Can't allocate on the heap in this context")
            val allocVd = env.expectAllocVdOpt(e.getPos, "calling a function that allocates")

            // Prepend the allocated set to the arguments
            newArgs +:= allocVd.toVariable
          
            // Assert that the new allocated set can only grow, and update it
            val checkSubset = SubsetOf(allocVd.toVariable, retAlloc).copiedFrom(e)
            val assign = Assignment(allocVd.toVariable, retAlloc).copiedFrom(e)
            block :+= Assert(checkSubset, None, assign).copiedFrom(e)
          }

          level match {
            case Some(writes) =>
              val heapVd = env.expectHeapVd(e.getPos, "effectful function call")

              // TODO: Only translate arguments once. This makes the substitution below a bit more
              // as we have to substitute the local bindings with the old type (to trigger the
              // correct ref transformation).
              val subst = (fi.tfd.params zip vargs).toMap
              val (reads, modifies) = heapContractsOf(fi.tfd.fullBody)
              val projected = projectHeap(subst, reads, heapVd)

              // Prepend the projected heap to the arguments
              newArgs +:= projected

              if (writes) {
                // If the callee reads and modifies the state, we need to unproject the heap that
                // it returned and update the local heap variable
                val unprojected = unprojectHeap(subst, modifies, heapVd, retHeap)
                block :+= Assignment(heapVd.toVariable, unprojected).copiedFrom(e)
              }
            case _ =>
          }
          
          // We ad the new arguments to the call
          val call = FunctionInvocation(id, targs1, newArgs).copiedFrom(e)

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
          val allocVd = env.expectAllocVdOpt(e.getPos, "checking allocation")
          ElementOfSet(ref, allocVd.toVariable).copiedFrom(e)

        case _ => super.transform(e, env)
      }

      override def transform(pat: Pattern, env: Env): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if livesInHeap(ct) =>
          val heapVd = env.expectHeapVd(pat.getPos, "class pattern unapply")
          val newClassPat = ClassPattern(
            None,
            classTypeInHeap(ct),
            subPats.map(transform(_, env))
          ).copiedFrom(pat)
          UnapplyPattern(
            binder.map(transform(_, env)),
            Seq(heapVd.toVariable),
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
        val allocs = exprOps.allocates(symbols.getFunction(fd.id))

        val heapVdOpt0 = if (reads) Some("heap0" :: HeapType) else None
        val heapVdOpt1 = if (writes) Some("heap1" :: HeapType) else None
        val allocVdOpt0 = if (allocs) Some("alloc0" :: HeapRefSet) else None
        val allocVdOpt1 = if (allocs) Some("alloc1" :: HeapRefSet) else None

        val newParams = heapVdOpt0.toSeq ++ allocVdOpt0.toSeq ++ fd.params.map(typeOnlyRefTransformer.transform)
        val newReturnType = transformReturnType(fd.returnType, writes, allocs)

        val (specs, bodyOpt) = deconstructSpecs(fd.fullBody)

        def transformPost(post: Expr, resVd: ValDef, valueVd: ValDef): Expr = {
          // Replace value result variable
          val replaceRes = resVd != valueVd
          val post1 = postMap {
            case v: Variable if replaceRes && v.id == resVd.id =>
              Some(valueVd.toVariable.copiedFrom(v))
            case _ =>
              None
          } (post)

          // Transform post condition body
          val post2 = transform(post1, specEnv(heapVdOpt1, allocVdOpt1))

          // Transform `old(...)` and `fresh(...)`
          postMap {
            case o @ Old(e) =>
              if (!writes)
                error(o.getPos, "Can't use 'old' in a function that does not modify the heap")

              Some(transform(e, specEnv(heapVdOpt0, allocVdOpt0)))

            case f @ Fresh(ref) =>
              if (!allocs)
                error(f.getPos, "Can't use 'fresh' in a non-allocating function")

              val notInAlloc0 = Not(ElementOfSet(ref, allocVdOpt0.getOrElse(dummyAllocatedVd).toVariable).copiedFrom(f)).copiedFrom(f)
              val inAlloc1 = ElementOfSet(ref, allocVdOpt1.getOrElse(dummyAllocatedVd).toVariable).copiedFrom(f)
              Some(And(Seq(notInAlloc0, inAlloc1)).copiedFrom(f))
            
            case _ =>
              None
          } (post2)
        }

        // TODO: Add readSet and writeSet instrumentation for specs
        val newSpecs = specs.collect {
          case Precondition(expr) =>
            Precondition(transform(expr, specEnv(heapVdOpt0, allocVdOpt0)))

          case Measure(expr) =>
            Measure(transform(expr, specEnv(heapVdOpt0, allocVdOpt0)))

          case Postcondition(lam @ Lambda(Seq(resVd), post)) =>
            val (resVd1, post1) = if (writes || allocs) {
              val valueVd: ValDef = "resV" :: resVd.tpe
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
            Postcondition(Lambda(Seq(resVd1), post1).copiedFrom(lam))
        }

        val newBodyOpt: Option[Expr] = bodyOpt.map { body =>
          val heapVdOpt = if (writes) Some("heap" :: HeapType) else heapVdOpt0
          val allocVdOpt = if (allocs) Some("alloc" :: HeapRefSet) else None

          // We build the resulting expression and the enclosing var definitions
          var results = Seq(transform(body, bodyEnv(writes, heapVdOpt, allocVdOpt)))
          var varDefs: Seq[(ValDef, Expr)] = Seq()

          if (writes) {
            results :+= heapVdOpt.get.toVariable
            varDefs :+= (heapVdOpt.get, heapVdOpt0.get.toVariable)
          }

          if (allocs) {
            results :+= allocVdOpt.get.toVariable
            varDefs :+= (allocVdOpt.get, allocVdOpt0.get.toVariable)
          }

          val newResult = tupleWrap(results)
          varDefs.foldRight(newResult) {
            case ((vd, value), acc) => LetVar(vd, value, acc)
          }
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
