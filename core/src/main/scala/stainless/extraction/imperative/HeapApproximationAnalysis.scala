/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.annotation.tailrec
import scala.collection.immutable.Queue

trait HeapApproximationAnalyses extends HeapApproximationGraphs {
  import s._

  /** The context of the phase running the analysis, for its options. */
  val context: inox.Context

  /** A parameter the function mutates, and the local variable `FunctionRewrite` copied it into. */
  case class MutatedParameter(param: Identifier, copy: Identifier)

  /** A function whose body the analysis can enter: a top-level function, a local function or a lambda. */
  sealed abstract class FunctionDefinition(using symbols: Symbols) {
    /** The parameters of the function. */
    def params: Seq[ValDef]

    /** The body of the function, without its specifications. */
    def body: Expr

    /** The free variables of the body that are not parameters, in a stable order. */
    lazy val capturedVariables: Seq[ValDef] = sorted(exprOps.variablesOf(body) -- params.map(_.toVariable))

    /** The control-flow graph of the body, over the parameters and the captured variables. */
    lazy val graph: HeapApproximationGraph = HeapApproximationGraph.build(params ++ capturedVariables, body)

    /** The parameters the function mutates, found from the copies `var copy = param` that `FunctionRewrite` adds. */
    lazy val mutatedParameters: Set[MutatedParameter] = exprOps.collect[MutatedParameter] {
      case LetVar(vd, Variable(id, _, _), _) if (params ++ capturedVariables).exists(param => param.id == id && symbols.isMutableType(param.tpe)) =>
        Set(MutatedParameter(id, vd.id))
      case _ =>
        Set.empty
    }(body)

    /** Whether a call to this function can reach it again. */
    def isRecursive: Boolean

    /** Whether calls to this function are summarized rather than entered. */
    def isOpaque: Boolean = isRecursive

    /** `variables` as declarations, in a stable order. */
    protected def sorted(variables: Set[Variable]): Seq[ValDef] =
      variables.toSeq.map(_.toVal).sortBy(_.id.uniqueName)
  }

  /** A top-level function. */
  case class GlobalFunctionDefinition(tfd: TypedFunDef)(using symbols: Symbols) extends FunctionDefinition {
    def params: Seq[ValDef] = tfd.params
    def body: Expr = exprOps.deconstructSpecs(tfd.fullBody)._2.get

    /** Whether the function has a body, rather than being abstract or external. */
    lazy val hasBody: Boolean = exprOps.deconstructSpecs(tfd.fullBody)._2.isDefined

    lazy val isRecursive: Boolean = symbols.isRecursive(tfd.id)
  }

  /** A function defined by a `LetRec`, with the local functions visible where it is defined. */
  case class LocalFunctionDefinition(fd: LocalFunDef, visible: Map[Identifier, LocalFunDef])(using Symbols) extends FunctionDefinition {
    def params: Seq[ValDef] = fd.params
    def body: Expr = LocalFunctionDefinition.bodyOf(fd)

    /** The visible local functions that a call to this one can reach. */
    lazy val reachableCalls: Set[Identifier] = {
      @tailrec
      def reach(pending: List[Identifier], visited: Set[Identifier]): Set[Identifier] = pending match {
        case Nil => visited
        case identifier :: rest if visited(identifier) || !visible.contains(identifier) => reach(rest, visited)
        case identifier :: rest => reach(rest ++ exprOps.innerFunctionCalls(LocalFunctionDefinition.bodyOf(visible(identifier))), visited + identifier)
      }

      reach(exprOps.innerFunctionCalls(body).toList, Set.empty)
    }

    lazy val isRecursive: Boolean = reachableCalls(fd.id)

    /** The free variables of this function and of the local functions it reaches, which are all in scope where it is defined. */
    override lazy val capturedVariables: Seq[ValDef] = {
      def freeVariables(local: LocalFunDef): Set[Variable] =
        exprOps.variablesOf(LocalFunctionDefinition.bodyOf(local)) -- local.params.map(_.toVariable)

      sorted(freeVariables(fd) ++ (reachableCalls - fd.id).flatMap(id => freeVariables(visible(id))))
    }
  }

  object LocalFunctionDefinition {
    /** The body of `local`, without its specifications. */
    def bodyOf(local: LocalFunDef): Expr = exprOps.deconstructSpecs(local.fullBody)._2.get
  }

  /** A lambda, always summarized. */
  case class LambdaFunctionDefinition(lambda: Lambda)(using Symbols) extends FunctionDefinition {
    def params: Seq[ValDef] = lambda.params
    def body: Expr = lambda.body

    val isRecursive: Boolean = false

    override val isOpaque: Boolean = true
  }

  /** The analysis of a local function or lambda body, kept to check it and to rewrite it later. */
  sealed abstract class FunctionAnalysis(using symbols: Symbols) {
    val definition: FunctionDefinition
    val analysis: HeapApproximationAnalysis

    /** The graph of the analyzed body. */
    private def graph: HeapApproximationGraph = definition.graph

    /** The captured mutable variables whose objects the body mutates, directly or by calling a local function that captures them. */
    def resolveCapturedMutations: Set[Identifier] = {
      def resolveReceiver(heap: HeapPointApproximation, receiver: Expr): HeapTargetSet =
        heap.resolveTargets(analysis.resolveLocation(heap, receiver))

      def resolveCalleeCaptures(heap: HeapPointApproximation, id: Identifier): HeapTargetSet = {
        val callee = analysis.resolveLocalFunction(id).filterNot(_.isRecursive)
        val captures = callee.toSeq.flatMap(_.capturedVariables).filter(vd => symbols.isMutableType(vd.tpe))

        HeapTargetSet.from(captures.flatMap(vd => heap.resolveAllTargets(HeapVariable(vd.id)).targets))
      }

      def resolveMutated(heap: HeapPointApproximation, e: Expr): HeapTargetSet = e match {
        case FieldAssignment(receiver, _, _) => resolveReceiver(heap, receiver)
        case ArrayUpdate(receiver, _, _) => resolveReceiver(heap, receiver)
        case MutableMapUpdate(receiver, _, _) => resolveReceiver(heap, receiver)
        case assignment @ WriteBack(_) => heap.resolveAllTargets(HeapVariable(assignment.v.id))
        case ApplyLetRec(id, _, _, _, _) => resolveCalleeCaptures(heap, id)
        case _ => HeapTargetSet(Set.empty)
      }

      def isMutated(variable: HeapVariable): Boolean = graph.points.values.exists { point =>
        analysis.heapAt.get(point.id).exists { heap =>
          !heap.resolveAllTargets(variable).intersect(resolveMutated(heap, point.e)).isEmpty
        }
      }

      definition.capturedVariables
        .filter(vd => symbols.isMutableType(vd.tpe))
        .map(vd => HeapVariable(vd.id))
        .filter(isMutated)
        .map(_.identifier)
        .toSet
    }

    /** Rejects a body that mutates an object reachable from a captured mutable variable. */
    def ensureNoCapturedMutation(): Unit = {
      if (resolveCapturedMutations.nonEmpty) {
        throw AliasingRewriteException.capturedMutation(definition.body)
      }
    }
  }

  /** The analysis of a local function. */
  case class LocalFunctionAnalysis(definition: LocalFunctionDefinition, analysis: HeapApproximationAnalysis)(using Symbols) extends FunctionAnalysis

  /** The analysis of a lambda. */
  case class LambdaFunctionAnalysis(definition: LambdaFunctionDefinition, analysis: HeapApproximationAnalysis)(using Symbols) extends FunctionAnalysis

  /** The heap at every program point of a function graph, with the functions analyzed so far. */
  case class HeapApproximationAnalysis(
    graph: HeapApproximationGraph,

    heapAt: Map[ExpressionID, HeapPointApproximation],

    definitions: Map[Identifier, FunctionDefinition] = Map.empty,
    functions: Map[ExpressionID, FunctionAnalysis] = Map.empty
  ) {
    /** The heap leaving `point`, without the results it read, empty when the point has not been reached yet. */
    def resolveHeapAt(point: ExpressionID): HeapPointApproximation =
      heapAt
        .get(point)
        .fold(HeapPointApproximation.empty(graph.scopeAt(point)))(_.withoutResults(graph.dependsOn(point)))

    /** The heap flowing into `point` from its single parent, pruned to the scope of the point. */
    def resolveParentHeap(point: ProgramPoint): HeapPointApproximation = {
      val parents = graph.parentsOf(point)

      if (parents.size > 1) {
        throw new IllegalStateException(s"${point.e} has several parents but is not a join point")
      }

      parents.headOption
        .fold(HeapPointApproximation.empty(point.scope))(parent => resolveHeapAt(parent.id))
        .prune(point.scope)
    }

    /** Records `heap` at `point`, after forgetting the variables of the graph that are dead there. */
    def withHeap(point: ProgramPoint, heap: HeapPointApproximation): HeapApproximationAnalysis = {
      val dead = heap.variables.collect { case HeapVariable(identifier) if graph.declared(identifier) && !point.live(identifier) => identifier }
      val pruned = heap
        .withoutReferencesOf(dead)
        .prune(heap.scope)

      copy(heapAt = heapAt + (point.id -> pruned))
    }

    /** The local function named `id`, if it is known. */
    def resolveLocalFunction(id: Identifier): Option[LocalFunctionDefinition] =
      definitions.get(id).collect { case definition: LocalFunctionDefinition => definition }

    /** Whether `call` is entered rather than summarized: its body is known and it is not recursive. */
    def isEntered(call: Expr)(using symbols: Symbols): Boolean = call match {
      case fi: FunctionInvocation => exprOps.deconstructSpecs(fi.tfd.fullBody)._2.isDefined && !symbols.isRecursive(fi.id)
      case ApplyLetRec(id, _, _, _, _) => resolveLocalFunction(id).exists(!_.isRecursive)
      case _ => false
    }

    /** The object `e` designates in `heap`, looking through bindings to the expression producing the value. */
    def resolveLocation(heap: HeapPointApproximation, e: Expr): HeapLocation =
      heap.results(graph.exitOf(e))

    /** The reference to the result of `e`, or none when `e` is not mutable. */
    def resolveExpression(heap: HeapPointApproximation, e: Expr)(using symbols: Symbols): HeapReference = {
      if (!symbols.isMutableType(e.getType)) {
        return NoHeapReference
      }

      ExactHeapReference(resolveLocation(heap, e))
    }

    /** Records the definition of the function `identifier`. */
    def withDefinition(identifier: Identifier, definition: FunctionDefinition): HeapApproximationAnalysis =
      copy(definitions = definitions + (identifier -> definition))

    /** Records the analysis of the function whose body is `body`. */
    private def withFunction(body: ExpressionID, function: FunctionAnalysis): HeapApproximationAnalysis =
      copy(functions = functions + (body -> function))

    /** This analysis and those of the functions nested in it. */
    def analyses: Seq[HeapApproximationAnalysis] =
      this +: functionAnalyses.map(_.analysis)

    /** The analyses of the functions nested in this one, at any depth. */
    def functionAnalyses: Seq[FunctionAnalysis] =
      functions.values.toSeq.flatMap(function => function +: function.analysis.functionAnalyses)

    /** Rejects an opaque function whose result or mutated parameters a caller could not rebuild from its summary: they must end as disjoint trees, apart from what the function received. */
    def ensureOpaque(definition: FunctionDefinition)(using Symbols): Unit = {
      def isCopy(e: Expr): Boolean = e match {
        case Variable(id, _, _) => definition.mutatedParameters.exists(_.copy == id)
        case _ => false
      }

      def reassignsCopy: Boolean = graph.points.values.exists {
        case ProgramPoint(_, assignment @ Assignment(v, _), _) => isCopy(v) && WriteBack.unapply(assignment).isEmpty
        case _ => false
      }

      def resolveReturned(exit: HeapPointApproximation): Set[HeapValue] = {
        def resultsOf(e: Expr): Seq[Expr] = e match {
          case Let(_, _, rest) => resultsOf(rest)
          case LetVar(_, _, rest) => resultsOf(rest)
          case Block(_, last) => resultsOf(last)
          case other => Seq(other)
        }

        val returns = exprOps.collect[Expr] {
          case Return(e) => Set(e)
          case _ => Set.empty
        }(definition.body)

        val returnedIDs = (resultsOf(definition.body) ++ returns)
          .map(ExpressionID(_))
          .toSet

        exit
          .resolveResult(graph.exitpoint)
          .flatMap {
            case tuple: HeapTuple if returnedIDs(ExpressionID(tuple.site.expr)) =>
              val Tuple(exprs) = tuple.site.expr: @unchecked
              val components = exprs.zipWithIndex.collect {
                case (component, index) if !isCopy(component) => exit.references(tuple.resolveSlot(TupleAccessor(index + 1)))
              }

              HeapReference.union(components)

            case target =>
              ExactHeapReference(target)
          }
          .toSet
          .collect { case value: HeapValue => value }
      }

      def returnsOriginal(exit: HeapPointApproximation): Boolean =
        resolveReturned(exit).exists(value => exit.resolveAllTargets(value).values.exists(_.isOriginal))

      def leavesEntangled(exit: HeapPointApproximation): Boolean =
        exit.results
          .get(graph.exitpoint)
          .exists(location => exit.isShared(location) || !exit.isTree(location))

      if (reassignsCopy) {
        throw AliasingRewriteException.reassignedCopy(definition.body)
      }

      val exit = resolveHeapAt(graph.exitpoint)

      if (returnsOriginal(exit)) {
        throw AliasingRewriteException.opaqueEffect(definition.body)
      }

      if (leavesEntangled(exit)) {
        throw AliasingRewriteException.nonFreshResult(definition.body)
      }
    }
  }

  /** Refines the heap of each program point from its parents, one expression at a time.
   *
   * The diagrams on the refiners use this notation:
   * {{{
   *   x --> o          the variable x points to o
   *   @e               the location holding the result of e
   *   o.f, o[i]        a slot of o: a field, a tuple component or an element
   *   o*               the elements of the collection o, shared by the collections pointing to it
   *   a | b            either a or b
   *   c ? a : b        a when c holds, b otherwise
   * }}}
   */
  object HeapApproximationAnalysis {
    /** How many times the heap of a point may change before the analysis gives up, set by `--heap-max-changes`. */
    private lazy val maxChanges: Int = context.options.findOptionOrDefault(optHeapMaxChanges)

    /** The points left to refine, with how often each one changed, to stop loops that do not converge. */
    private case class HeapWorklist(pending: Queue[ExpressionID], changes: Map[ExpressionID, Int] = Map.empty) {
      /** Whether no point is left to refine. */
      def isEmpty: Boolean = pending.isEmpty

      /** The next point to refine, and the worklist without it. */
      def dequeue: (ExpressionID, HeapWorklist) = {
        val (point, rest) = pending.dequeue

        (point, copy(pending = rest))
      }

      /** Schedules the successors of `point`, whose heap changed. */
      def changed(point: ProgramPoint, successors: Seq[ProgramPoint]): HeapWorklist = {
        val count = changes.getOrElse(point.id, 0) + 1

        if (count > maxChanges) {
          throw AliasingRewriteException.nonConvergentLoop(point.e)
        }

        val successorIDs = successors
          .map(_.id)
          .filterNot(pending.contains)

        copy(pending = pending ++ successorIDs, changes = changes.updated(point.id, count))
      }
    }

    /** Analyzes a top-level function. */
    def refineDefinition(tfd: TypedFunDef)(using symbols: Symbols): HeapApproximationAnalysis = {
      val definition = GlobalFunctionDefinition(tfd)

      refineFunction(HeapApproximationAnalysis(definition.graph, Map.empty), definition)
    }

    /** Analyzes a specification, such as a postcondition, as a lambda over the variables it reads. */
    def refineSpecification(lambda: Lambda)(using symbols: Symbols): HeapApproximationAnalysis = {
      val definition = LambdaFunctionDefinition(lambda)

      refineFunction(HeapApproximationAnalysis(definition.graph, Map.empty), definition)
    }

    /** Analyzes the body of `definition` from its parameters, knowing the functions of `enclosing`. */
    private def refineFunction(enclosing: HeapApproximationAnalysis, definition: FunctionDefinition)(using symbols: Symbols): HeapApproximationAnalysis = {
      val graph = definition.graph
      val entryHeap = HeapPointApproximation.initial(graph.scopeAt(graph.entrypoint), graph.params)
      val analysis = refineBody(enclosing.copy(graph = graph, heapAt = Map(graph.entrypoint -> entryHeap), functions = Map.empty))

      if (definition.isOpaque) {
        analysis.ensureOpaque(definition)
      }

      analysis
    }

    /** Refines the points of the graph until no heap changes. */
    private def refineBody(analysis: HeapApproximationAnalysis)(using symbols: Symbols): HeapApproximationAnalysis = {
      @tailrec
      def refineFixpoint(analysis: HeapApproximationAnalysis, worklist: HeapWorklist): HeapApproximationAnalysis = {
        if (worklist.isEmpty) {
          return analysis
        }

        val (pointID, rest) = worklist.dequeue
        val point = analysis.graph.points(pointID)

        val newAnalysis = refineExpression(analysis, point)
        val changed = newAnalysis.heapAt.get(pointID) != analysis.heapAt.get(pointID)

        val newWorklist = if (changed) rest.changed(point, analysis.graph.nextOf(point)) else rest

        refineFixpoint(newAnalysis, newWorklist)
      }

      val graph = analysis.graph
      val start = graph.transitions(graph.entrypoint).head

      refineFixpoint(analysis, HeapWorklist(Queue(start)))
    }

    /** Refines `point` according to the kind of its expression. */
    private def refineExpression(analysis: HeapApproximationAnalysis, point: ProgramPoint)(using symbols: Symbols): HeapApproximationAnalysis = {
      point.e match {
        case _ if point.id == analysis.graph.exitpoint => refineExit(analysis, point)

        case e: IfExpr => refineIf(analysis, point, e)
        case e: While  => refineWhile(analysis, point, e)

        case e: Let    => refineLet(analysis, point, e)
        case e: LetVar => refineLetVar(analysis, point, e)
        case e: LetRec => refineLetRec(analysis, point, e)

        case e @ WriteBack(_)    => refineWriteBack(analysis, point, e)
        case e: Assignment       => refineAssignment(analysis, point, e)
        case e: FieldAssignment  => refineFieldAssignment(analysis, point, e)
        case e: ArrayUpdate      => refineArrayUpdate(analysis, point, e)
        case e: MutableMapUpdate => refineMutableMapUpdate(analysis, point, e)

        case e: Block  => refineBlock(analysis, point, e)
        case e: Lambda => refineLambda(analysis, point, e)

        case _: And | _: Or | _: Not | _: Implies => refineUntracked(analysis, point)

        case e: FunctionInvocation => refineInvocation(analysis, point, e)
        case e: ApplyLetRec        => refineApplyLetRec(analysis, point, e)
        case e: Application        => refineApplication(analysis, point, e)
        case e: ArraySelect        => refineArraySelect(analysis, point, e)
        case e: MutableMapApply    => refineMutableMapApply(analysis, point, e)

        case e if isImmutableCollection(e.getType) => refineUntracked(analysis, point)
        case e if !symbols.isMutableType(e.getType) => refineUntracked(analysis, point)

        case e: FreshCopy => refineExternal(analysis, point)
        case e: Snapshot  => refineExternal(analysis, point)

        case e: Variable      => refineVariable(analysis, point, e)
        case e: ClassSelector => refineClassSelector(analysis, point, e)
        case e: TupleSelect   => refineTupleSelect(analysis, point, e)

        case e: ClassConstructor => refineClassConstructor(analysis, point, e)
        case e: Tuple            => refineTuple(analysis, point, e)

        case e: FiniteArray  => refineFiniteArray(analysis, point, e)
        case e: LargeArray   => refineLargeArray(analysis, point, e)
        case e: ArrayUpdated => refineArrayUpdated(analysis, point, e)

        case e: MutableMapWithDefault => refineMutableMapWithDefault(analysis, point, e)
        case e: MutableMapUpdated     => refineMutableMapUpdated(analysis, point, e)
        case e: MutableMapDuplicate   => refineMutableMapDuplicate(analysis, point, e)

        case e: Annotated    => refineAnnotated(analysis, point, e)
        case e: AsInstanceOf => refineAsInstanceOf(analysis, point, e)
        case e: Assert       => refineAssert(analysis, point, e)
        case e: Assume       => refineAssume(analysis, point, e)
        case e: Decreases    => refineDecreases(analysis, point, e)
        case e: Old          => refineOld(analysis, point, e)

        case e: Error  => refineError(analysis, point, e)
        case e: Choose => refineChoose(analysis, point, e)

        case e => throw AliasingRewriteException.unsupportedConstruct(e)
      }
    }

    /** Whether values of `tpe` are sets or bags, which never hold mutable objects. */
    private def isImmutableCollection(tpe: Type)(using symbols: Symbols): Boolean = tpe.getType match {
      case _: SetType | _: BagType => true
      case _ => false
    }

    /** What storing `value` into a slot puts there: the object it designates, or the immutable value written at this site. */
    private def resolveContent(analysis: HeapApproximationAnalysis, heap: HeapPointApproximation, value: Expr)(using symbols: Symbols): (HeapReference, HeapPointApproximation) = {
      if (symbols.isMutableType(value.getType)) {
        return (heap.dereference(analysis.resolveExpression(heap, value)), heap)
      }

      val (immutable, registered) = heap.withImmutable(ExpressionID(value))

      (ExactHeapReference(immutable), registered)
    }

    /** Passes the parent heap through: nothing is created.
     *
     * {{{
     *   H  ==>  H
     * }}}
     */
    private def refineUntracked(analysis: HeapApproximationAnalysis, point: ProgramPoint)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      analysis.withHeap(point, heap)
    }

    /** Joins the returning points and records what the function returns.
     *
     * {{{
     *   return a   ...   b      @exit --> o_a | o_b
     * }}}
     */
    private def refineExit(analysis: HeapApproximationAnalysis, point: ProgramPoint)(using symbols: Symbols): HeapApproximationAnalysis = {
      val graph = analysis.graph
      val parents = graph.parentsOf(point)

      val parentHeaps = parents.flatMap(parent => analysis.heapAt.get(parent.id))
      val mergedHeap = HeapPointApproximation.merge(point.scope, parentHeaps)

      val returned = parents.map { parent =>
        val result = parent.e match {
          case Return(inner) => inner
          case e => e
        }

        mergedHeap.resolveResult(graph.exitOf(result))
      }

      val resultHeap = mergedHeap
        .withoutResults(graph.points.keySet)
        .withExpressionResult(point.e, HeapReference.union(returned))

      val finalHeap = resultHeap
        .withoutConditionOn(graph.locals)
        .prune(point.scope)

      analysis.withHeap(point, finalHeap)
    }

    /** Joins the two branches, making what they disagree on conditional on the condition.
     *
     * {{{
     *   then:  x --> a
     *   else:  x --> b    ==>    x --> c ? a : b
     *                            @if --> c ? @then : @else
     * }}}
     */
    private def refineIf(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: IfExpr)(using symbols: Symbols): HeapApproximationAnalysis = {
      val graph = analysis.graph

      def reaches(branch: Expr): Boolean =
        graph.parentsOf(point).exists(_.id == graph.exitOf(branch))

      def branchHeap(branch: Expr): HeapPointApproximation = {
        if (!reaches(branch)) {
          return HeapPointApproximation.empty(point.scope)
        }

        analysis
          .resolveHeapAt(graph.exitOf(branch))
          .prune(point.scope)
      }

      val IfExpr(condition, thenn, elze) = e

      val thenHeap = branchHeap(thenn)
      val elzeHeap = branchHeap(elze)

      val mergedHeap = thenHeap.mergeWithCondition(condition, elzeHeap)

      val branchlessHeap = mergedHeap
        .withoutResults(thenn)
        .withoutResults(elze)

      if (!symbols.isMutableType(e.getType)) {
        return analysis.withHeap(point, branchlessHeap)
      }

      val thenResult = mergedHeap.resolveResult(graph.exitOf(thenn))
      val elzeResult = mergedHeap.resolveResult(graph.exitOf(elze))
      val result = (reaches(thenn), reaches(elze)) match {
        case (true, false) => thenResult
        case (false, true) => elzeResult
        case _ => HeapReference.conditional(condition, thenResult, elzeResult)
      }

      val finalHeap = branchlessHeap.withExpressionResult(e, result)

      analysis.withHeap(point, finalHeap)
    }

    /** Joins the loop entry with the previous iteration, whose new objects are relocated to stay apart from the current ones.
     *
     * {{{
     *   entry:     x --> a
     *   back edge: x --> n       (n created by the body)
     *   head:      x --> a | n'  (n' is n, relocated to the previous iteration)
     * }}}
     */
    private def refineWhile(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: While)(using symbols: Symbols): HeapApproximationAnalysis = {
      val graph = analysis.graph
      val backEdge = graph.exitOf(e.body)

      val entryHeaps = graph
        .parentsOf(point)
        .filter(_.id != backEdge)
        .map(parent => analysis.resolveHeapAt(parent.id))

      val headHeaps = entryHeaps ++ analysis.heapAt.get(point.id)
      val entryHeap = HeapPointApproximation
        .merge(point.scope, headHeaps)
        .prune(point.scope)

      val backHeap = analysis.resolveHeapAt(backEdge)

      if (backHeap.isEmpty) {
        return analysis.withHeap(point, entryHeap)
      }

      val previousIteration = ExpressionRegistry(ExpressionID(e))
      val iterationHeap = backHeap.withoutResults(e)
      val relocatedHeap = iterationHeap
        .created(entryHeap)
        .foldLeft(iterationHeap)((heap, created) => heap.withRelocate(previousIteration, created))
        .prune(point.scope)

      val mergedHeap = HeapPointApproximation.merge(point.scope, Seq(entryHeap, relocatedHeap))
      val outsideHeap = HeapPointApproximation.merge(point.scope, entryHeaps :+ relocatedHeap)

      val finalHeap = mergedHeap.references.references.keySet
        .foldLeft(mergedHeap) { (heap, holder) =>
          if (relocatedHeap.references.get(holder).isEmpty || !relocatedHeap.isFresh(holder)) {
            heap
          } else {
            heap.withReference(holder, outsideHeap.references(holder))
          }
        }
        .prune(point.scope)

      analysis.withHeap(point, finalHeap)
    }

    /** The block results in its last expression.
     *
     * {{{
     *   @{ ...; e } --> @e
     * }}}
     */
    private def refineBlock(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Block)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val cleared = heap.withoutResults(e)

      if (!symbols.isMutableType(e.getType)) {
        return analysis.withHeap(point, cleared)
      }

      val result = analysis.resolveExpression(heap, e.last)

      val refined = cleared
        .withExpressionResult(e, result)
        .withExpressionResult(e.last, result)

      analysis.withHeap(point, refined)
    }

    /** `val x = e`: see `refineDeclaration`. */
    private def refineLet(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Let)(using symbols: Symbols): HeapApproximationAnalysis =
      refineDeclaration(analysis, point, e.vd, e.value)

    /** `var x = e`: see `refineDeclaration`. */
    private def refineLetVar(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: LetVar)(using symbols: Symbols): HeapApproximationAnalysis =
      refineDeclaration(analysis, point, e.vd, e.value)

    /** Declares `vd`, pointing to the result of `value`.
     *
     * {{{
     *   @e --> o    ==>    x --> o
     * }}}
     */
    private def refineDeclaration(analysis: HeapApproximationAnalysis, point: ProgramPoint, vd: ValDef, value: Expr)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val result = analysis.resolveExpression(heap, value)

      val refined = heap
        .withDeclareVariable(vd.id, result)
        .withoutResults(value)

      analysis.withHeap(point, refined)
    }

    /** Makes the variable point to the result of the assigned value.
     *
     * {{{
     *   x --> old    ==>    x --> o    (@e --> o)
     * }}}
     */
    private def refineAssignment(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Assignment)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val result = analysis.resolveExpression(heap, e.value)

      val refined = heap
        .withAssignVariable(e.v.id, result)
        .withoutResults(e.value)

      analysis.withHeap(point, refined)
    }

    /** A write back of a copy changes nothing: the copy already shares its objects. */
    private def refineWriteBack(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Assignment)(using symbols: Symbols): HeapApproximationAnalysis =
      refineUntracked(analysis, point)

    /** The variable results in what it points to.
     *
     * {{{
     *   x --> o    ==>    @x --> o
     * }}}
     */
    private def refineVariable(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Variable)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      analysis.withHeap(point, heap.withExpressionResult(e, heap.resolveVariable(e.id)))
    }

    /** Analyzes the lambda body once; the lambda itself is not tracked. */
    private def refineLambda(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Lambda)(using symbols: Symbols): HeapApproximationAnalysis = {
      if (analysis.functions.contains(ExpressionID(e.body))) {
        return refineUntracked(analysis, point)
      }

      val definition = LambdaFunctionDefinition(e)
      val function = LambdaFunctionAnalysis(definition, refineFunction(analysis, definition))
      function.ensureNoCapturedMutation()

      refineUntracked(analysis.withFunction(ExpressionID(e.body), function), point)
    }

    /** Analyzes each local function body once; the definitions themselves are not tracked. */
    private def refineLetRec(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: LetRec)(using symbols: Symbols): HeapApproximationAnalysis = {
      val withBodies = e.fds.filter(fd => exprOps.deconstructSpecs(fd.fullBody)._2.isDefined)
      val visible = analysis.definitions.collect { case (id, local: LocalFunctionDefinition) => id -> local.fd } ++
        withBodies.map(fd => fd.id -> fd)

      val defined = withBodies
        .filterNot(fd => analysis.definitions.contains(fd.id))
        .foldLeft(analysis)((analysis, fd) => analysis.withDefinition(fd.id, LocalFunctionDefinition(fd, visible)))

      val functionsAnalysis = e.fds
        .flatMap(fd => defined.resolveLocalFunction(fd.id))
        .filterNot(definition => defined.functions.contains(ExpressionID(definition.body)))
        .foldLeft(defined) { (analysis, definition) =>
          val function = LocalFunctionAnalysis(definition, refineFunction(analysis, definition))

          if (definition.isRecursive) {
            function.ensureNoCapturedMutation()
          }

          analysis.withFunction(ExpressionID(definition.body), function)
        }

      refineUntracked(functionsAnalysis, point)
    }

    /** A call to a top-level function: entered when its body is known and not recursive, summarized otherwise. */
    private def refineInvocation(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: FunctionInvocation)(using symbols: Symbols): HeapApproximationAnalysis = {
      val definition = analysis.definitions
        .get(e.id)
        .collect { case definition: GlobalFunctionDefinition if definition.tfd == e.tfd => definition }
        .getOrElse(GlobalFunctionDefinition(e.tfd))
      val defined = analysis.withDefinition(e.id, definition)

      if (!definition.hasBody || definition.mutatedParameters.nonEmpty) {
        ensureDistinctArguments(defined, point, e.args)
      }

      if (!symbols.isMutableType(e.getType)) {
        return refineUntracked(defined, point)
      }

      if (!defined.isEntered(e)) {
        return refineExternal(defined, point)
      }

      refineCall(defined, point, definition)
    }

    /** A call to a local function: entered when known and not recursive, summarized otherwise. */
    private def refineApplyLetRec(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ApplyLetRec)(using symbols: Symbols): HeapApproximationAnalysis = {
      val definition = analysis.resolveLocalFunction(e.id)
      val captured = definition.toSeq
        .flatMap(_.capturedVariables)
        .filter(vd => symbols.isMutableType(vd.tpe))
        .map(vd => HeapVariable(vd.id))

      ensureDistinctArguments(analysis, point, e.args, captured)

      if (!symbols.isMutableType(e.getType)) {
        return refineUntracked(analysis, point)
      }

      definition match {
        case Some(entered) if analysis.isEntered(e) => refineCall(analysis, point, entered)
        case _ => refineExternal(analysis, point)
      }
    }

    /** A call to a lambda value: always summarized. */
    private def refineApplication(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Application)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureDistinctArguments(analysis, point, e.args)

      if (!symbols.isMutableType(e.getType)) {
        return refineUntracked(analysis, point)
      }

      refineExternal(analysis, point)
    }

    /** Enters the callee with its parameters bound to the arguments, and imports its effects and result.
     *
     * {{{
     *   caller:  a --> o                      f(a), where def f(p) = { p.g = C(); p }
     *   callee:  p --> o,  o.g --> n
     *   after:   a --> o,  o.g --> n',  @f(a) --> o    (n' is n, relocated to the call)
     * }}}
     */
    private def refineCall(analysis: HeapApproximationAnalysis, point: ProgramPoint, definition: FunctionDefinition)(using symbols: Symbols): HeapApproximationAnalysis = {
      val e = point.e
      val Operator(args, _) = e: @unchecked

      val heap = analysis.resolveParentHeap(point)

      val capturedVariables = definition.capturedVariables.map(vd => heap.resolveVariable(vd.id))
      val arguments = args.map(analysis.resolveExpression(heap, _)) ++ capturedVariables

      if (arguments.exists(heap.isAmbiguous)) {
        throw AliasingRewriteException.unimportableCall(e)
      }

      val graph = definition.graph
      val scope = graph.scopeAt(graph.entrypoint)
      val scopedHeap = heap.withScope(scope)

      val initialHeap = graph.params
        .zip(arguments)
        .foldLeft(scopedHeap) { case (heap, (vd, argument)) => heap.withReassignVariable(vd.id, argument) }
        .withRestriction(graph.params.map(_.id).toSet)

      val entryAnalysis = analysis.copy(graph = graph, heapAt = Map(graph.entrypoint -> initialHeap))
      val resultAnalysis = refineBody(entryAnalysis)
      val resultHeap = resultAnalysis.resolveHeapAt(graph.exitpoint) match {
        case heap if !heap.isEmpty => heap
        case _ => initialHeap
      }

      val bindings = definition.params.zip(args).toMap
      val unstable = bindings.collect { case (vd, arg) if !isStable(arg) => vd.id }.toSet
      val translatedResultHeap = resultHeap
        .withoutConditionOn(unstable)
        .withSubstitution(bindings)

      val context = ExpressionRegistry(ExpressionID(e))
      val relocatedResultHeap = translatedResultHeap
        .created(initialHeap)
        .foldLeft(translatedResultHeap)((heap, value) => heap.withRelocate(context, value))

      val finalHeap = heap
        .withOverride(relocatedResultHeap)
        .withExpressionResult(e, relocatedResultHeap.resolveResult(graph.exitpoint))

      analysis
        .copy(definitions = resultAnalysis.definitions)
        .withHeap(point, finalHeap)
    }

    /** Results in a fresh value whose content is unknown.
     *
     * {{{
     *   @e --> v    (v fresh)
     * }}}
     */
    private def refineExternal(analysis: HeapApproximationAnalysis, point: ProgramPoint)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val (value, registered) = heap.withValue(ExpressionID(point.e), point.e.getType)

      analysis.withHeap(point, registered.withExpressionResult(point.e, ExactHeapReference(value)))
    }

    /** `r.f`: see `refineSlotSelect`. */
    private def refineClassSelector(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ClassSelector)(using symbols: Symbols): HeapApproximationAnalysis =
      refineSlotSelect(analysis, point, e.expr, FieldAccessor(e.selector))

    /** `r._i`: see `refineSlotSelect`. */
    private def refineTupleSelect(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: TupleSelect)(using symbols: Symbols): HeapApproximationAnalysis =
      refineSlotSelect(analysis, point, e.tuple, TupleAccessor(e.index))

    /** `a(i)`: see `refineSlotSelect`. */
    private def refineArraySelect(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ArraySelect)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureUnshared(analysis, point, e.array)

      if (!symbols.isMutableType(e.getType)) {
        return refineUntracked(analysis, point)
      }

      refineSlotSelect(analysis, point, e.array, ElementAccessor(e.index))
    }

    /** `m(k)`: see `refineSlotSelect`. */
    private def refineMutableMapApply(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: MutableMapApply)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureUnshared(analysis, point, e.map)

      if (!symbols.isMutableType(e.getType)) {
        return refineUntracked(analysis, point)
      }

      refineSlotSelect(analysis, point, e.map, ElementAccessor(e.key))
    }

    /** Reads a slot of the receiver, giving a name to its original content the first time it is read.
     *
     * {{{
     *   @r --> o,  o.f --> original           ==>    original --> v,  @r.f --> v    (v names the original, o.f is unchanged)
     *   @r --> o,  o.f --> w                  ==>    @r.f --> w
     *   @r --> o1 | o2,  o1.f --> original    ==>    o1.f --> v | original,  @r.f --> v | ...    (only one of them is read)
     * }}}
     */
    private def refineSlotSelect(analysis: HeapApproximationAnalysis, point: ProgramPoint, receiver: Expr, accessor: HeapAccessor)(using symbols: Symbols): HeapApproximationAnalysis = {
      val e = point.e
      val heap = analysis.resolveParentHeap(point)

      val location = analysis.resolveLocation(heap, receiver)
      val values = heap.resolveValues[HeapValue](location).filter(_.hasSlot(accessor))

      val (original, registered) = heap.withValue(ExpressionID(e), e.getType)
      val contents = values
        .map(owner => owner -> heap.dereference(heap.references(HeapSlot(owner, accessor))).withOriginal(original))
        .toMap[HeapObject, HeapReference]

      val owners = heap.dereference(ExactHeapReference(location))
      val observed = owners match {
        case ExactHeapReference(owner: HeapValue) if values(owner) =>
          val slot = HeapSlot(owner, accessor)
          val unread = heap.dereference(heap.references(slot)).toSet.collect { case unread: HeapOriginal => unread }

          unread.foldLeft(registered.withReference(slot, heap.references(slot))) { (heap, unread) =>
            heap.withReference(unread, ExactHeapReference(original))
          }

        case _ =>
          values.foldLeft(registered) { (heap, owner) =>
            val slot = HeapSlot(owner, accessor)

            heap.withReference(slot, owners.flatMap(candidate => if (candidate == owner) contents(owner) else heap.references(slot)))
          }
      }

      val result = owners.flatMap(owner => contents.getOrElse(owner, NoHeapReference))

      analysis.withHeap(point, observed.withExpressionResult(e, result))
    }

    /** `r.f = e`: see `refineSlotAssignment`. */
    private def refineFieldAssignment(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: FieldAssignment)(using symbols: Symbols): HeapApproximationAnalysis =
      refineSlotAssignment(analysis, point, e.obj, FieldAccessor(e.selector), e.value)

    /** `a(i) = e`: see `refineSlotAssignment`. */
    private def refineArrayUpdate(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ArrayUpdate)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureUnshared(analysis, point, e.array)

      refineSlotAssignment(analysis, point, e.array, ElementAccessor(e.index), e.value)
    }

    /** `m(k) = e`: see `refineSlotAssignment`. */
    private def refineMutableMapUpdate(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: MutableMapUpdate)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureUnshared(analysis, point, e.map)

      refineSlotAssignment(analysis, point, e.map, ElementAccessor(e.key), e.value)
    }

    /** Writes a slot of the receiver; when the receiver is conditional, each candidate is written only on its branch.
     *
     * {{{
     *   @r --> o,         @e --> w    ==>    o.f --> w
     *   @r --> c ? o : p, @e --> w    ==>    o.f --> c ? w : old,  p.f --> c ? old : w
     * }}}
     */
    private def refineSlotAssignment(analysis: HeapApproximationAnalysis, point: ProgramPoint, receiver: Expr, accessor: HeapAccessor, value: Expr)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val location = analysis.resolveLocation(heap, receiver)
      val values = heap.resolveValues[HeapValue](location).filter(_.hasSlot(accessor))

      val owners = heap.dereference(ExactHeapReference(location))
      val (reference, stored) = resolveContent(analysis, heap, value)
      val refined = values.foldLeft(stored) { (heap, owner) =>
        val slot = HeapSlot(owner, accessor)

        heap.withReference(slot, owners.flatMap(candidate => if (candidate == owner) reference else heap.references(slot)))
      }

      analysis.withHeap(point, refined)
    }

    /** `C(a, b)`: see `refineConstructor`. */
    private def refineClassConstructor(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ClassConstructor)(using symbols: Symbols): HeapApproximationAnalysis =
      refineConstructor(analysis, point, e.ct.tcd.fields.map(vd => FieldAccessor(vd.id)).zip(e.args))

    /** `(a, b)`: see `refineConstructor`. */
    private def refineTuple(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Tuple)(using symbols: Symbols): HeapApproximationAnalysis =
      refineConstructor(analysis, point, e.exprs.zipWithIndex.map((component, index) => TupleAccessor(index + 1) -> component))

    /** `Array(a, b)`: see `refineConstructor`. */
    private def refineFiniteArray(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: FiniteArray)(using symbols: Symbols): HeapApproximationAnalysis =
      refineConstructor(analysis, point, e.elems.zipWithIndex.map((element, index) => ElementAccessor(Int32Literal(index)) -> element))

    /** `Array.fill(n)(d)` with some elements given: see `refineConstructor`. */
    private def refineLargeArray(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: LargeArray)(using symbols: Symbols): HeapApproximationAnalysis = {
      ensureFreshDefault(analysis, point, e.default)

      refineConstructor(analysis, point, e.elems.toSeq.map((index, element) => ElementAccessor(Int32Literal(index)) -> element))
    }

    /** A new map with a default: see `refineExternal`. */
    private def refineMutableMapWithDefault(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: MutableMapWithDefault)(using symbols: Symbols): HeapApproximationAnalysis =
      refineExternal(analysis, point)

    /** Creates a fresh value whose slots point to the results of `components`.
     *
     * {{{
     *   @a --> x,  @b --> y    ==>    n.f1 --> x,  n.f2 --> y,  @C(a, b) --> n    (n fresh)
     * }}}
     */
    private def refineConstructor(analysis: HeapApproximationAnalysis, point: ProgramPoint, components: Seq[(HeapAccessor, Expr)])(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val (value, registered) = heap.withValue(ExpressionID(point.e), point.e.getType)
      val initialized = components.foldLeft(registered) { case (heap, (accessor, component)) =>
        val (content, stored) = resolveContent(analysis, heap, component)

        stored.withReference(HeapSlot(value, accessor), content)
      }

      analysis.withHeap(point, initialized.withExpressionResult(point.e, ExactHeapReference(value)))
    }

    /** `a.updated(i, e)`: see `refineCollectionUpdated`. */
    private def refineArrayUpdated(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: ArrayUpdated)(using symbols: Symbols): HeapApproximationAnalysis =
      refineCollectionUpdated(analysis, point, e.array, e.index, e.value)

    /** `m.updated(k, e)`: see `refineCollectionUpdated`. */
    private def refineMutableMapUpdated(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: MutableMapUpdated)(using symbols: Symbols): HeapApproximationAnalysis =
      refineCollectionUpdated(analysis, point, e.map, e.key, e.value)

    /** Creates a fresh collection sharing its elements with the source, then writes one element.
     *
     * {{{
     *   s --> s*    ==>    s --> s* | n*,  n --> s* | n*,  n[i] --> w,  @e --> n    (n fresh, @e --> w)
     * }}}
     */
    private def refineCollectionUpdated(analysis: HeapApproximationAnalysis, point: ProgramPoint, source: Expr, index: Expr, value: Expr)(using symbols: Symbols): HeapApproximationAnalysis = {
      val e = point.e
      val heap = analysis.resolveParentHeap(point)

      val location = analysis.resolveLocation(heap, source)

      if (CallResult.isWithin(value)) {
        return analysis.withHeap(point, heap.withExpressionResult(e, ExactHeapReference(location)))
      }

      val (collection, registered) = heap.withCollection(e)

      if (!hasMutableElements(e)) {
        return analysis.withHeap(point, registered.withExpressionResult(e, ExactHeapReference(collection)))
      }

      val sources = heap.resolveValues[HeapCollection](location)
      val elements = sources.foldLeft(registered.references(collection))((elements, source) => elements.union(registered.references(source)))
      val (reference, stored) = resolveContent(analysis, registered, value)
      val updated = (sources + collection)
        .foldLeft(stored)((heap, shared) => heap.withReference(shared, elements))
        .withAssignElement(collection, index, reference)

      analysis.withHeap(point, updated.withExpressionResult(e, ExactHeapReference(collection)))
    }

    /** Creates a fresh map sharing its elements with the source, with a copy of each known element.
     *
     * {{{
     *   m --> m*,  m[k] --> w    ==>    m --> m* | n*,  n --> m* | n*,  n[k] --> w,  @e --> n    (n fresh)
     * }}}
     */
    private def refineMutableMapDuplicate(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: MutableMapDuplicate)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      val (collection, registered) = heap.withCollection(e)

      if (!hasMutableElements(e)) {
        return analysis.withHeap(point, registered.withExpressionResult(e, ExactHeapReference(collection)))
      }

      val sources = heap.resolveValues[HeapCollection](analysis.resolveLocation(heap, e.map))
      val elements = sources.foldLeft(registered.references(collection))((elements, source) => elements.union(registered.references(source)))
      val shared = (sources + collection).foldLeft(registered)((heap, shared) => heap.withReference(shared, elements))

      val slots = sources.toSeq
        .flatMap(shared.resolveSlots)
        .collect { case slot: HeapElement => slot }

      val copied = slots.foldLeft(shared) { (heap, slot) =>
        val element = heap.references
          .get(collection.resolveSlot(slot.accessor))
          .fold(heap.references(slot))(_.union(heap.references(slot)))

        heap.withAssignElement(collection, slot.index, element)
      }

      analysis.withHeap(point, copied.withExpressionResult(e, ExactHeapReference(collection)))
    }

    /** Whether the elements of the collection `e` are mutable. */
    private def hasMutableElements(e: Expr)(using symbols: Symbols): Boolean = e.getType.getType match {
      case ArrayType(base) => symbols.isMutableType(base)
      case MutableMapType(_, to) => symbols.isMutableType(to)
      case _ => false
    }

    /** An annotation: see `refineInner`. */
    private def refineAnnotated(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Annotated)(using symbols: Symbols): HeapApproximationAnalysis =
      refineInner(analysis, point, e.body)

    /** A cast: see `refineInner`. */
    private def refineAsInstanceOf(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: AsInstanceOf)(using symbols: Symbols): HeapApproximationAnalysis =
      refineInner(analysis, point, e.expr)

    /** An assertion: see `refineInner`. */
    private def refineAssert(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Assert)(using symbols: Symbols): HeapApproximationAnalysis =
      refineInner(analysis, point, e.body)

    /** An assumption: see `refineInner`. */
    private def refineAssume(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Assume)(using symbols: Symbols): HeapApproximationAnalysis =
      refineInner(analysis, point, e.body)

    /** A measure: see `refineInner`. */
    private def refineDecreases(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Decreases)(using symbols: Symbols): HeapApproximationAnalysis =
      refineInner(analysis, point, e.body)

    /** An `old` outside a postcondition, which a later phase rejects: see `refineExternal`. */
    private def refineOld(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Old)(using symbols: Symbols): HeapApproximationAnalysis =
      refineExternal(analysis, point)

    /** Results in the result of `inner`.
     *
     * {{{
     *   @inner --> o    ==>    @e --> o
     * }}}
     */
    private def refineInner(analysis: HeapApproximationAnalysis, point: ProgramPoint, inner: Expr)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      analysis.withHeap(point, heap.withExpressionResult(point.e, analysis.resolveExpression(heap, inner)))
    }

    /** An error results in nothing.
     *
     * {{{
     *   @e --> (nothing)
     * }}}
     */
    private def refineError(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Error)(using symbols: Symbols): HeapApproximationAnalysis = {
      val heap = analysis.resolveParentHeap(point)

      analysis.withHeap(point, heap.withExpressionResult(e, NoHeapReference))
    }

    /** A `choose`: see `refineExternal`. */
    private def refineChoose(analysis: HeapApproximationAnalysis, point: ProgramPoint, e: Choose)(using symbols: Symbols): HeapApproximationAnalysis =
      refineExternal(analysis, point)

    /** Whether `arg` keeps its object, or its value when immutable, wherever a condition mentioning it is evaluated. */
    private def isStable(arg: Expr)(using symbols: Symbols): Boolean = arg match {
      case v: Variable => !v.flags.contains(IsVar)
      case _ => symbols.isImmutableExpression(arg)
    }

    /** Rejects a collection that other objects may also point to. */
    private def ensureUnshared(analysis: HeapApproximationAnalysis, point: ProgramPoint, collection: Expr)(using symbols: Symbols): Unit = {
      if (!symbols.isMutableType(collection.getType)) {
        return
      }

      val heap = analysis.resolveParentHeap(point)

      if (heap.isShared(analysis.resolveLocation(heap, collection))) {
        throw AliasingRewriteException.sharedCollection(collection)
      }
    }

    /** Rejects arguments, or captured variables, that reach a common object or that are not trees. */
    private def ensureDistinctArguments(analysis: HeapApproximationAnalysis, point: ProgramPoint, args: Seq[Expr], captured: Seq[HeapObject] = Seq.empty)(using symbols: Symbols): Unit = {
      args.foreach(ensureUnshared(analysis, point, _))

      val heap = analysis.resolveParentHeap(point)
      val sources = args
        .filter(arg => symbols.isMutableType(arg.getType))
        .map(arg => analysis.resolveLocation(heap, arg)) ++ captured

      val reachable = sources.map(heap.resolveAllTargets)
      val overlapping = reachable
        .combinations(2)
        .exists { case Seq(first, second) => !first.intersect(second).isEmpty }

      val entangled = sources.exists(source => !heap.isTree(source))

      if (overlapping || entangled) {
        throw AliasingRewriteException.sharedArgument(point.e)
      }
    }

    /** Rejects a mutable array default that is not a fresh value. */
    private def ensureFreshDefault(analysis: HeapApproximationAnalysis, point: ProgramPoint, default: Expr)(using symbols: Symbols): Unit = {
      if (!symbols.isMutableType(default.getType)) {
        return
      }

      val heap = analysis.resolveParentHeap(point)

      if (!heap.isFresh(analysis.resolveLocation(heap, default))) {
        throw AliasingRewriteException.nonFreshDefault(default)
      }
    }
  }
}
