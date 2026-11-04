/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.annotation.tailrec
import scala.collection.immutable.Queue

trait HeapApproximationAnalyses extends HeapApproximationGraphs {
  import s._

  sealed abstract class FunctionAnalysis {
    val analysis: HeapApproximationAnalysis

    def params: Seq[ValDef]
    def body: Expr

    def capturedVariables: Seq[ValDef] = HeapApproximationAnalysis.capturedVariables(params, body)

    def exitHeap: HeapPointApproximation =
      analysis.heapAt.getOrElse(analysis.graph.exitpoint, HeapPointApproximation.empty(analysis.graph.points(analysis.graph.exitpoint).scope))
  }

  case class LocalFunctionAnalysis(fd: LocalFunDef, analysis: HeapApproximationAnalysis) extends FunctionAnalysis {
    def params: Seq[ValDef] = fd.params
    def body: Expr = exprOps.deconstructSpecs(fd.fullBody)._2.get
  }

  case class LambdaAnalysis(lambda: Lambda, analysis: HeapApproximationAnalysis) extends FunctionAnalysis {
    def params: Seq[ValDef] = lambda.params
    def body: Expr = lambda.body
  }

  case class GlobalFunctionAnalysis(tfd: TypedFunDef, analysis: HeapApproximationAnalysis) extends FunctionAnalysis {
    def params: Seq[ValDef] = tfd.params
    def body: Expr = exprOps.deconstructSpecs(tfd.fullBody)._2.get
  }

  type ParameterPosition = (Int, Seq[HeapAccessor])

  type CallFacts = (Map[Seq[HeapAccessor], Set[Option[ParameterPosition]]], Map[ParameterPosition, Set[Option[ParameterPosition]]])

  case class HeapApproximationAnalysis(
    graph: HeapApproximationGraph,
    
    heapAt: Map[ExpressionID, HeapPointApproximation],
    functions: Map[ExpressionID, FunctionAnalysis] = Map.empty,
    externals: Map[ExpressionID, HeapPointApproximation] = Map.empty,
    group: Set[Identifier] = Set.empty,
    facts: Map[Identifier, CallFacts] = Map.empty
  ) {
    private def withHeapAt(point: ExpressionID, heap: HeapPointApproximation): HeapApproximationAnalysis =
      copy(heapAt = heapAt + (point -> heap))

    private def withFunction(body: ExpressionID, function: FunctionAnalysis): HeapApproximationAnalysis =
      copy(functions = functions + (body -> function))

    private def withExternal(point: ExpressionID, heap: HeapPointApproximation): HeapApproximationAnalysis =
      copy(externals = externals + (point -> heap))
  }

  object HeapApproximationAnalysis {
    private case class HeapWorklist(pending: Queue[ExpressionID], changes: Map[ExpressionID, Int] = Map.empty) {
      private val maxChanges = 10

      def isEmpty: Boolean = pending.isEmpty

      def dequeue: (ExpressionID, HeapWorklist) = {
        val (point, rest) = pending.dequeue
        (point, copy(pending = rest))
      }

      def changed(point: Point, successors: Seq[Point]): HeapWorklist = {
        val count = changes.getOrElse(point.id, 0) + 1
        if (count > maxChanges) {
          throw AliasingAssignRewriteException.nonConvergentLoop(point.e)
        }

        copy(pending = pending ++ successors.map(_.id).filterNot(pending.contains), changes = changes.updated(point.id, count))
      }
    }

    private val maxRounds = 10

    def refineDefinition(id: Identifier, params: Seq[ValDef], body: Expr, functions: Map[ExpressionID, FunctionAnalysis] = Map.empty)(using Symbols): HeapApproximationAnalysis = {
      val group = recursiveGroup(id)
      if (group.isEmpty) {
        return refineFunction(params, body, functions, Set.empty, Map.empty)
      }

      refineFunction(params, body, functions, group, groupFacts(group, body))
    }

    private def recursiveGroup(id: Identifier)(using symbols: Symbols): Set[Identifier] = {
      if (!symbols.isRecursive(id)) {
        return Set.empty
      }

      symbols.functions.keySet.filter(other => other == id || (symbols.transitivelyCalls(id, other) && symbols.transitivelyCalls(other, id)))
    }

    private def groupFacts(group: Set[Identifier], tree: Expr)(using symbols: Symbols): Map[Identifier, CallFacts] = {
      @tailrec
      def iterate(facts: Map[Identifier, CallFacts], round: Int): Map[Identifier, CallFacts] = {
        if (round > maxRounds) {
          throw AliasingAssignRewriteException.nonConvergentRecursion(tree)
        }

        val next = group.toSeq.flatMap { id =>
          val fd = symbols.getFunction(id)
          exprOps.deconstructSpecs(fd.fullBody)._2.flatMap { body =>
            val analysis = refineFunction(fd.params, body, Map.empty, group, facts)
            callFacts(GlobalFunctionAnalysis(fd.typed, analysis)).map(id -> _)
          }
        }.toMap

        if (next == facts) facts else iterate(next, round + 1)
      }

      iterate(Map.empty, 0)
    }

    def refineWithHeap(graph: HeapApproximationGraph, entryHeap: HeapPointApproximation, functions: Map[ExpressionID, FunctionAnalysis], group: Set[Identifier], facts: Map[Identifier, CallFacts])(using symbols: Symbols): HeapApproximationAnalysis = {
      @tailrec
      def refineFixpoint(analysis: HeapApproximationAnalysis, worklist: HeapWorklist): HeapApproximationAnalysis = {
        if (worklist.isEmpty) {
          return analysis
        }

        val (pointID, rest) = worklist.dequeue
        val point = graph.points(pointID)
        checkInvariant(analysis, point)
        val (newAnalysis, changed) = point.e match {
          case lambda: Lambda => refineLambda(analysis, point, lambda)
          case letRec: LetRec => refineLetRec(analysis, point, letRec)
          case e: FunctionInvocation => refineInvocation(analysis, point, e)
          case _: ApplyLetRec | _: Application | _: FreshCopy | _: Snapshot => refineExternal(analysis, point)
          case e @ (_: ArraySelect | _: MutableMapApply) if isMutableType(e.getType) => refineObservation(analysis, point)
          case _ => refinePoint(analysis, point)
        }
        val newWorklist = if (changed) rest.changed(point, graph.nextOf(point)) else rest

        refineFixpoint(newAnalysis, newWorklist)
      }

      val initialAnalysis = HeapApproximationAnalysis(graph, Map(graph.entrypoint -> entryHeap), functions, group = group, facts = facts)

      refineFixpoint(initialAnalysis, HeapWorklist(Queue(graph.transitions(graph.entrypoint).head)))
    }

    def initializeHeap(params: Seq[ValDef], scope: Int)(using Symbols): HeapPointApproximation =
      params.foldLeft(HeapPointApproximation.empty(scope)) { (heap, vd) =>
        val (location, initializedHeap) = initializeObject(heap, vd.toVariable)
        
        initializedHeap.withDeclareVariable(vd.id, location)
      }

    def initializeExternal(e: Expr, scope: Int)(using Symbols): HeapPointApproximation = {
      val (location, initializedHeap) = initializeObject(HeapPointApproximation.empty(scope), e)

      initializedHeap.withExpressionResult(e, location)
    }

    private def initializeObject(heap: HeapPointApproximation, path: Expr)(using Symbols): (HeapLocation, HeapPointApproximation) = {
      val (reference, representation) = recursiveLocation(ExpressionID(path), heap.scope).representation

      heap.merge(representation).withLocation(path, reference)
    }

    private def recursiveLocation(site: ExpressionID, scope: Int)(using Symbols): HeapRecursiveAddress =
      HeapRecursiveAddress(site)(initializeRepresentation(_, scope))

    private def initializeRepresentation(recursive: HeapRecursiveAddress, scope: Int)(using Symbols): (HeapReference, HeapPointApproximation) = {
      val context = recursive.site.context

      def initializeChild(heap: HeapPointApproximation, path: Expr): (HeapAddress, HeapPointApproximation) = {
        if (isRecursiveType(path.getType)) {
          return heap.withRecursiveLocation(recursiveLocation(ExpressionID(context, path), heap.scope))
        }

        val (reference, initializedHeap) = initializeInstance(heap, path)
        initializedHeap.withLocation(ExpressionID(context, path), reference)
      }

      def initializeInstance(heap: HeapPointApproximation, path: Expr): (HeapReference, HeapPointApproximation) = {
        if (!isTrackedType(path)) {
          return (NoHeapReference, heap)
        }

        def initializeClass(heap: HeapPointApproximation, instance: HeapInstance, ct: ClassType): HeapPointApproximation =
          (ct.tcd +: ct.tcd.descendants).foldLeft(heap) { (heap, tcd) =>
            val receiver = if (tcd == ct.tcd) path else AsInstanceOf(path, tcd.toType).copiedFrom(path)
            val fields = tcd.fields.map(vd => ClassSelector(receiver, vd.id).copiedFrom(path))

            fields.foldLeft(heap) { (heap, field) =>
              val (location, fieldHeap) = initializeChild(heap, field)
              fieldHeap.withAssignField(instance, field.selector, location)
            }
          }

        def initializeTuple(heap: HeapPointApproximation, instance: HeapInstance, bases: Seq[Type]): HeapPointApproximation = {
          val components = bases.indices.map(index => TupleSelect(path, index + 1).copiedFrom(path))

          components.foldLeft(heap) { (heap, component) =>
            val (location, componentHeap) = initializeChild(heap, component)
            componentHeap.withAssignTuple(instance, component.index, location)
          }
        }

        val tpe = path.getType.getType
        val (instance, allocatedHeap) = heap.withAllocation(ExpressionID(context, path))
        val initializedHeap = tpe match {
          case ct: ClassType => initializeClass(allocatedHeap, instance, ct)
          case TupleType(bases) => initializeTuple(allocatedHeap, instance, bases)
          case ArrayType(_) | MutableMapType(_, _) => allocatedHeap.withCollection(instance)
          case _ => allocatedHeap
        }

        (ExactHeapReference(instance), initializedHeap)
      }

      initializeInstance(HeapPointApproximation.empty(scope), recursive.site.expr)
    }

    private def isRecursiveType(tpe: Type)(using Symbols): Boolean = {
      def components(tpe: Type): Seq[Type] = tpe match {
        case ct: ClassType => (ct.tcd +: ct.tcd.descendants).flatMap(_.fields.map(_.tpe))
        case TupleType(bases) => bases
        case _ => Seq.empty
      }

      @tailrec
      def reaches(pending: List[Type], visited: Set[Type]): Boolean = pending match {
        case Nil => false
        case head :: _ if head == tpe => true
        case head :: rest if visited(head) || !isMutableType(head) => reaches(rest, visited)
        case head :: rest => reaches(components(head).toList ++ rest, visited + head)
      }

      reaches(components(tpe).toList, Set.empty)
    }

    def refinePoint(analysis: HeapApproximationAnalysis, point: Point)(using symbols: Symbols): (HeapApproximationAnalysis, Boolean) = {
      val parentHeap = this.parentHeap(analysis, point)
      val localHeap = analysis.externals.get(point.id).fold(refineHeap(analysis.graph, parentHeap, point.e))(parentHeap.merge)

      withHeap(analysis, point, localHeap)
    }

    private def parentHeap(analysis: HeapApproximationAnalysis, point: Point)(using Symbols): HeapPointApproximation = point.e match {
      case e: IfExpr => mergeBranches(analysis, point, e)
      case e: While => loopHeap(analysis, point, e)
      case _ => mergeParents(analysis, point)
    }

    private def mergeParents(analysis: HeapApproximationAnalysis, point: Point): HeapPointApproximation =
      analysis.graph.parentsOf(point).flatMap(parent => analysis.heapAt.get(parent.id)).reduceOption(_.merge(_)).getOrElse(HeapPointApproximation.empty(point.scope)).prune(point.scope)

    private def loopHeap(analysis: HeapApproximationAnalysis, point: Point, e: While)(using Symbols): HeapPointApproximation = {
      val backEdge = analysis.graph.exitOf(e.body)

      def incoming(parents: Set[ExpressionID]): Option[HeapPointApproximation] =
        parents.toSeq.flatMap(analysis.heapAt.get).map(_.withoutResults(e.cond).withoutResults(e.body).prune(point.scope)).reduceOption(_.merge(_))

      val parents = analysis.graph.parents.getOrElse(point.id, Set.empty)
      val entry = incoming(parents - backEdge).getOrElse(HeapPointApproximation.empty(point.scope))

      incoming(Set(backEdge)).fold(entry) { back =>
        val carried = point.live.filter { identifier =>
          back.resolveTargets(HeapVariable(identifier)).targets.exists(target => !entry.isAlive(target.instance))
        }

        def owned(heap: HeapPointApproximation, identifier: Identifier): Boolean =
          heap.isFresh(HeapVariable(identifier)) && heap.isDisjoint(HeapVariable(identifier))

        if (carried.exists(identifier => !owned(entry, identifier) || !owned(back, identifier))) throw AliasingAssignRewriteException.leakingVariable(e)

        val restarted = back.collect(carried).prune(point.scope)
        val iteration = restarted.iterationElements(entry)

        if (iteration.exists(slot => !restarted.isFresh(slot))) throw AliasingAssignRewriteException.leakingElement(e)

        entry.merge(restarted.withoutElements(iteration))
      }
    }

    private def withHeap(analysis: HeapApproximationAnalysis, point: Point, heap: HeapPointApproximation): (HeapApproximationAnalysis, Boolean) = {
      val dead = heap.objects.keySet.collect { case HeapVariable(identifier) if !point.live(identifier) => identifier }
      val liveHeap = heap.collect(dead).prune(heap.scope).withUnsharedElements.prune(heap.scope)

      (analysis.withHeapAt(point.id, liveHeap), !analysis.heapAt.get(point.id).contains(liveHeap))
    }

    private def mergeBranches(analysis: HeapApproximationAnalysis, point: Point, e: IfExpr)(using Symbols): HeapPointApproximation = {
      val IfExpr(cond, thenn, elze) = e
      val condition = cond match {
        case variable: Variable => variable
        case _ => throw new IllegalStateException(s"ConditionalHoisting should have hoisted the condition of $e")
      }

      def branchHeap(branch: Expr): HeapPointApproximation = {
        val exit = analysis.graph.exitOf(branch)
        if (!analysis.graph.parents.getOrElse(point.id, Set.empty)(exit)) {
          return HeapPointApproximation.empty(point.scope)
        }

        analysis.heapAt.get(exit).fold(HeapPointApproximation.empty(point.scope))(_.prune(point.scope))
      }

      branchHeap(thenn).mergeConditional(conditionOf(analysis.graph, condition), branchHeap(elze))
    }

    private def refineObservation(analysis: HeapApproximationAnalysis, point: Point)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      val observed = if (analysis.externals.contains(point.id)) analysis else analysis.withExternal(point.id, initializeExternal(point.e, point.scope))

      withHeap(observed, point, refineHeap(observed.graph, parentHeap(observed, point).merge(observed.externals(point.id)), point.e))
    }

    private def refineExternal(analysis: HeapApproximationAnalysis, point: Point)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      if (analysis.externals.contains(point.id)) {
        return refinePoint(analysis, point)
      }

      refinePoint(analysis.withExternal(point.id, initializeExternal(point.e, point.scope)), point)
    }

    private def refineInvocation(analysis: HeapApproximationAnalysis, point: Point, e: FunctionInvocation)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      if (analysis.group(e.id)) {
        return refineGroupCall(analysis, point, e)
      }

      val body = exprOps.deconstructSpecs(e.tfd.fullBody)._2
      if (body.isEmpty || !isMutableType(e.getType)) {
        return refineExternal(analysis, point)
      }

      val summarized =
        if (analysis.functions.contains(ExpressionID(body.get))) analysis
        else analysis.withFunction(ExpressionID(body.get), GlobalFunctionAnalysis(e.tfd, refineDefinition(e.id, e.tfd.params, body.get, analysis.functions)))
      val function = summarized.functions(ExpressionID(body.get))

      importCall(function, this.parentHeap(summarized, point), e, summarized.graph).fold {
        throw AliasingAssignRewriteException.unimportableCall(e)
      } { case (reference, importedHeap) =>
        val (location, newHeap) = importedHeap.withLocation(e, reference)

        withHeap(summarized, point, newHeap.withExpressionResult(e, location))
      }
    }

    private def refineGroupCall(analysis: HeapApproximationAnalysis, point: Point, e: FunctionInvocation)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      val facts = analysis.facts.get(e.id)
      if (facts.isEmpty) {
        return (analysis, false)
      }

      val observed = if (analysis.externals.contains(point.id)) analysis else analysis.withExternal(point.id, initializeExternal(point.e, point.scope))
      val heap = parentHeap(observed, point).merge(observed.externals(point.id))

      withHeap(observed, point, withFacts(observed.graph, heap, e, facts.get))
    }

    private def withFacts(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: FunctionInvocation, facts: CallFacts)(using Symbols): HeapPointApproximation = {
      val (resultFacts, writeFacts) = facts

      def resolvePath(heap: HeapPointApproximation, root: HeapReference, accessors: Seq[HeapAccessor]): (HeapReference, HeapPointApproximation) =
        accessors.foldLeft((root, heap)) { case ((reference, heap), accessor) =>
          reference.toSet().foldLeft((NoHeapReference: HeapReference, heap)) { case ((result, heap), owner) =>
            val (component, resolvedHeap) = resolveComponent(heap, owner, accessor)
            (result.union(component), resolvedHeap)
          }
        }

      def resolveComponent(heap: HeapPointApproximation, owner: HeapObject, accessor: HeapAccessor): (HeapReference, HeapPointApproximation) = accessor match {
        case FieldAccessor(identifier) => heap.resolveField(owner, identifier)
        case TupleAccessor(index) => heap.resolveTuple(owner, index)
        case ElementAccessor(_) => throw AliasingAssignRewriteException.unimportableCall(e)
      }

      def componentOf(owner: HeapObject, accessor: HeapAccessor): HeapObject = accessor match {
        case FieldAccessor(identifier) => HeapInstanceField(owner, identifier)
        case TupleAccessor(index) => HeapTupleField(owner, index)
        case ElementAccessor(_) => throw AliasingAssignRewriteException.unimportableCall(e)
      }

      def valueOf(heap: HeapPointApproximation, targets: Set[Option[ParameterPosition]]): (HeapReference, HeapPointApproximation) =
        targets.toSeq.flatten.foldLeft((NoHeapReference: HeapReference, heap)) { case ((result, heap), (index, accessors)) =>
          val (reference, resolvedHeap) = resolvePath(heap, ExactHeapReference(resolveExpression(graph, heap, e.args(index))), accessors)
          (result.union(reference), resolvedHeap)
        }

      def holdersAt(heap: HeapPointApproximation, root: HeapReference, accessors: Seq[HeapAccessor]): (Seq[HeapObject], HeapPointApproximation) = {
        val (owners, ownersHeap) = resolvePath(heap, root, accessors.init)
        owners.toSet().flatMap(ownersHeap.references.resolve).toSeq.foldLeft((Seq.empty[HeapObject], ownersHeap)) { case ((holders, heap), owner) =>
          val (_, resolvedHeap) = resolveComponent(heap, owner, accessors.last)
          (holders :+ componentOf(owner, accessors.last), resolvedHeap)
        }
      }

      val location = heap.results(ExpressionID(e))
      val root = ExactHeapReference(location)

      val (resultUpdates, resultHeap) = resultFacts.toSeq.sortBy(-_._1.size).foldLeft((Seq.empty[(Seq[HeapObject], Set[Option[ParameterPosition]], HeapReference)], heap)) { case ((updates, heap), (path, targets)) =>
        val (value, valueHeap) = valueOf(heap, targets)
        if (path.isEmpty) {
          (updates :+ ((Seq(location), targets, value)), valueHeap)
        } else {
          val (holders, holdersHeap) = holdersAt(valueHeap, root, path)
          (updates :+ ((holders, targets, value)), holdersHeap)
        }
      }

      val (writeUpdates, writeHeap) = writeFacts.toSeq.foldLeft((Seq.empty[(Seq[HeapObject], Set[Option[ParameterPosition]], HeapReference)], resultHeap)) { case ((updates, heap), ((index, accessors), targets)) =>
        val (value, valueHeap) = valueOf(heap, targets)
        val (holders, holdersHeap) = holdersAt(valueHeap, ExactHeapReference(resolveExpression(graph, valueHeap, e.args(index))), accessors)
        (updates :+ ((holders, targets, value)), holdersHeap)
      }

      (resultUpdates ++ writeUpdates).foldLeft(writeHeap) { case (heap, (holders, targets, value)) =>
        holders.foldLeft(heap) { (heap, holder) =>
          heap.withReference(holder, if (targets(None)) heap.references(holder).union(value) else value)
        }
      }
    }

    private def importCall(function: FunctionAnalysis, heap: HeapPointApproximation, e: FunctionInvocation, graph: HeapApproximationGraph)(using Symbols): Option[(HeapReference, HeapPointApproximation)] = {
      val effect = calleeEffect(function)
      if (effect.isEmpty) {
        return None
      }

      val (result, writes, structures, created, heads) = effect.get
      val callsite = ExpressionID(e)

      val (combinations, embeddedHeap) = structures.toSeq.foldLeft((Seq(Seq.empty[(HeapObjectStructure, HeapObjectStructure)]), heap)) { case ((combinations, heap), (index, structure)) =>
        val roots = heap.resolveTargets(resolveExpression(graph, heap, e.args(index))).targets.toSeq.map(_.instance)
        val (representations, representationsHeap) = roots.foldLeft((Seq.empty[HeapObjectRepresentation], heap)) { case ((representations, heap), root) =>
          val (representation, representationHeap) = heap.embed(root, structure).getOrElse(throw AliasingAssignRewriteException.unimportableCall(e))
          (representations :+ representation, representationHeap)
        }
        val extended = for {
          combination <- combinations
          representation <- representations
          alternative <- representation.alternatives
        } yield combination :+ (structure -> alternative)

        (extended, representationsHeap)
      }

      def instancesOf(structure: HeapObjectStructure): Seq[HeapObject] =
        structure.instance +: structure.children.values.toSeq.flatMap(instancesOf)

      val registeredHeap = created.foldLeft(embeddedHeap) {
        case (heap, instance: HeapInstance) =>
          val (imported, allocatedHeap) = heap.withAllocation(instance.within(callsite).asInstanceOf[HeapInstance].site)
          if (heads(instance)) allocatedHeap.withCollection(imported) else allocatedHeap

        case (heap, recursive: HeapRecursiveAddress) =>
          heap.withRecursiveLocation(recursive.within(callsite))._2

        case (heap, _) => heap
      }

      val alternatives = combinations.map { combination =>
        val callerInstances = combination.flatMap { case (_, alternative) => instancesOf(alternative) }
        if (callerInstances.distinct.size != callerInstances.size) {
          throw AliasingAssignRewriteException.sharedArgument(e)
        }

        val substitution = HeapSubstitution.union(combination.map { case (structure, alternative) => structure.substitution(alternative) })

        def imported(heapObject: HeapObject): HeapObject = heapObject match {
          case HeapInstanceField(owner, identifier) => HeapInstanceField(imported(owner), identifier)
          case HeapTupleField(owner, index) => HeapTupleField(imported(owner), index)
          case target if created(target) => target.within(callsite)
          case target => target.substitute(substitution)
        }

        def importedReference(reference: HeapReference): HeapReference =
          reference.mapLeaves(NoHeapReference)(target => ExactHeapReference(imported(target)))

        val overlaid = writes.foldLeft(registeredHeap) { case (heap, (field, value)) => heap.withReference(imported(field), importedReference(value)) }

        (importedReference(result), overlaid)
      }

      val imported = (alternatives.map(_._1).foldLeft(NoHeapReference: HeapReference)(_.union(_)), alternatives.map(_._2).reduceOption(_.merge(_)).getOrElse(registeredHeap))
      Some(imported)
    }

    private def isInternalSite(graph: HeapApproximationGraph, site: ExpressionID): Boolean =
      site.context.isDefined || graph.points.contains(ExpressionID(HeapAccessor.fromExpression(site.expr)._1))

    private def siteOf(target: HeapObject): Option[ExpressionID] = target match {
      case HeapLocation(site) => Some(site)
      case HeapInstance(site) => Some(site)
      case recursive: HeapRecursiveAddress => Some(recursive.site)
      case _ => None
    }

    private def parameterPositionOf(function: FunctionAnalysis, site: ExpressionID): Option[ParameterPosition] = {
      if (isInternalSite(function.analysis.graph, site)) {
        return None
      }

      HeapAccessor.fromExpression(site.expr) match {
        case (Variable(id, _, _), accessors) if accessors.forall(!_.isInstanceOf[ElementAccessor]) =>
          Some(function.params.indexWhere(_.id == id)).filter(_ >= 0).map(_ -> accessors)
        case _ => None
      }
    }

    private def fieldPositionOf(function: FunctionAnalysis, field: HeapObject): Option[ParameterPosition] = field match {
      case HeapInstanceField(HeapInstance(site), identifier) => parameterPositionOf(function, site).map { case (index, accessors) => (index, accessors :+ FieldAccessor(identifier)) }
      case HeapTupleField(HeapInstance(site), component) => parameterPositionOf(function, site).map { case (index, accessors) => (index, accessors :+ TupleAccessor(component)) }
      case _ => None
    }

    private def callFacts(function: FunctionAnalysis)(using Symbols): Option[CallFacts] = {
      if (!function.analysis.heapAt.contains(function.analysis.graph.exitpoint)) {
        return None
      }

      val (result, writes, _, created, _) = calleeEffect(function).getOrElse(throw AliasingAssignRewriteException.unimportableCall(function.body))
      val components = writes.toMap

      def describe(reference: HeapReference): Set[Option[ParameterPosition]] =
        reference.toSet().map { target =>
          if (created(target)) None
          else Some(siteOf(target).flatMap(parameterPositionOf(function, _)).getOrElse(throw AliasingAssignRewriteException.unimportableCall(function.body)))
        }

      def united(maps: Seq[Map[Seq[HeapAccessor], Set[Option[ParameterPosition]]]]): Map[Seq[HeapAccessor], Set[Option[ParameterPosition]]] =
        maps.foldLeft(Map.empty[Seq[HeapAccessor], Set[Option[ParameterPosition]]]) { (result, map) =>
          map.foldLeft(result) { case (result, (path, targets)) => result.updated(path, result.getOrElse(path, Set.empty) ++ targets) }
        }

      def walk(path: Seq[HeapAccessor], reference: HeapReference, visited: Set[HeapObject]): Map[Seq[HeapAccessor], Set[Option[ParameterPosition]]] = {
        val owners = reference.toSet().filter(target => created(target) && !visited(target))
        val deeper = owners.toSeq.flatMap { owner =>
          components.toSeq.collect {
            case (HeapInstanceField(`owner`, identifier), value) => walk(path :+ FieldAccessor(identifier), value, visited ++ owners)
            case (HeapTupleField(`owner`, index), value) => walk(path :+ TupleAccessor(index), value, visited ++ owners)
          }
        }

        united(Map(path -> describe(reference)) +: deeper)
      }

      val writeFacts = writes.flatMap { case (field, value) => fieldPositionOf(function, field).map(_ -> describe(value)) }.toMap

      Some((walk(Seq.empty, result, Set.empty).filter(_._2.exists(_.isDefined)), writeFacts.filter(_._2.exists(_.isDefined))))
    }

    private def calleeEffect(function: FunctionAnalysis)(using Symbols): Option[(HeapReference, Seq[(HeapObject, HeapReference)], Map[Int, HeapObjectStructure], Set[HeapObject], Set[HeapObject])] = {
      val graph = function.analysis.graph
      val exitHeap = function.exitHeap
      if (exitHeap.isEmpty) {
        return Some((NoHeapReference, Seq.empty, Map.empty, Set.empty, Set.empty))
      }

      def isInternal(site: ExpressionID): Boolean = isInternalSite(graph, site)
      def parameterPosition(site: ExpressionID): Option[ParameterPosition] = parameterPositionOf(function, site)
      def fieldPosition(field: HeapObject): Option[ParameterPosition] = fieldPositionOf(function, field)

      val parameterSlotWrite = graph.points.values.exists { point =>
        val written = point.e match {
          case ArrayUpdate(array, _, value) if isMutableType(value.getType) => Some(array)
          case MutableMapUpdate(map, _, value) if isMutableType(value.getType) => Some(map)
          case _ => None
        }

        written.exists { collection =>
          function.analysis.heapAt.get(point.id).exists { heap =>
            heap.resolveTargets(resolveExpression(graph, heap, collection)).targets.exists(target => parameterPosition(target.instance.site).isDefined)
          }
        }
      }
      if (parameterSlotWrite) {
        return None
      }

      def isUnchanged(field: HeapObject, position: (Int, Seq[HeapAccessor])): Boolean = exitHeap.references(field) match {
        case ExactHeapReference(address: HeapAddress) => siteOf(address).flatMap(parameterPosition).contains(position)
        case _ => false
      }

      def collapse(reference: HeapReference, visited: Set[HeapObject]): HeapReference =
        reference.toSet().foldLeft(NoHeapReference: HeapReference) {
          case (result, recursive: HeapRecursiveAddress) if isInternal(recursive.site) && exitHeap.references(recursive) == NoHeapReference => result.union(ExactHeapReference(recursive))
          case (result, address: HeapAddress) => result.union(if (visited(address)) NoHeapReference else collapse(exitHeap.references(address), visited + address))
          case (result, target) => result.union(ExactHeapReference(target))
        }

      def componentsOf(instance: HeapObject): Seq[HeapObject] =
        exitHeap.objects(instance).children.toSeq.collect { case component @ (_: HeapInstanceField | _: HeapTupleField) => component }

      def fresh(targets: Set[HeapObject], visited: Set[HeapObject]): Set[HeapObject] = {
        val reached = targets.filter {
          case HeapInstance(site) => isInternal(site) && !visited(HeapInstance(site))
          case recursive: HeapRecursiveAddress => isInternal(recursive.site) && !visited(recursive)
          case _ => false
        }
        if (reached.isEmpty) {
          return visited
        }

        val next = reached.toSeq.flatMap {
          case instance: HeapInstance => componentsOf(instance).flatMap(component => collapse(exitHeap.references(component), Set.empty).toSet())
          case _ => Seq.empty
        }.toSet

        fresh(next, visited ++ reached)
      }

      val returned = returnedExpressions(function.body).map(resolveExpression(graph, exitHeap, _))
      val result = collapse(returned.foldLeft(NoHeapReference: HeapReference)((result, location) => result.union(ExactHeapReference(location))), Set.empty)

      val written = exitHeap.objects.keySet.toSeq.filter(field => fieldPosition(field).exists(!isUnchanged(field, _)))
      val created = fresh(result.toSet() ++ written.flatMap(field => collapse(exitHeap.references(field), Set.empty).toSet()), Set.empty)
      val heads = created.collect { case instance: HeapInstance if exitHeap.isAlive(HeapElements(instance)) => instance: HeapObject }
      if (heads.exists(head => exitHeap.references(head) != ExactHeapReference(HeapElements(head.asInstanceOf[HeapInstance])))) {
        return None
      }

      val writes = (written ++ created.toSeq.flatMap(componentsOf)).map(field => field -> collapse(exitHeap.references(field), Set.empty))
      val owners = written.collect { case HeapInstanceField(owner, _) => owner; case HeapTupleField(owner, _) => owner }
      val used = (result.toSet() ++ owners ++ writes.flatMap(_._2.toSet())) -- created
      val usedPositions = used.toSeq.flatMap(target => siteOf(target).flatMap(parameterPosition))
      if (usedPositions.size != used.size) {
        return None
      }

      val parameterInstances = exitHeap.objects.keySet.toSeq.flatMap {
        case instance @ HeapInstance(site) => parameterPosition(site).map(_ -> (instance: HeapObject))
        case _ => None
      }.toMap
      val positions = usedPositions.toSet.flatMap { case (index, accessors) => accessors.inits.map(index -> _) }

      def structureAt(position: (Int, Seq[HeapAccessor])): HeapObjectStructure = {
        val (index, accessors) = position
        val children = positions.collect { case (`index`, path) if path.nonEmpty && path.init == accessors => path.last -> structureAt((index, path)) }.toMap

        HeapObjectStructure(parameterInstances(position), children)
      }

      Some((result, writes, positions.collect { case (index, Seq()) => index -> structureAt((index, Seq.empty)) }.toMap, created, heads))
    }

    def capturedVariables(params: Seq[ValDef], body: Expr): Seq[ValDef] =
      (exprOps.variablesOf(body) -- params.map(_.toVariable)).toSeq.map(_.toVal).sortBy(_.id.uniqueName)

    private def refineFunction(params: Seq[ValDef], body: Expr, functions: Map[ExpressionID, FunctionAnalysis], group: Set[Identifier], facts: Map[Identifier, CallFacts])(using Symbols): HeapApproximationAnalysis = {
      val graph = HeapApproximationGraph.build(params ++ capturedVariables(params, body), body)

      refineWithHeap(graph, initializeHeap(graph.params, graph.points(graph.entrypoint).scope), functions, group, facts)
    }

    private def refineLambda(analysis: HeapApproximationAnalysis, point: Point, lambda: Lambda)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      if (analysis.functions.contains(ExpressionID(lambda.body))) {
        return refinePoint(analysis, point)
      }

      val function = LambdaAnalysis(lambda, refineFunction(lambda.params, lambda.body, analysis.functions, Set.empty, Map.empty))
      checkReturn(function.analysis, function.params ++ function.capturedVariables, function.body, imported = false)
      checkNoCapturedMutation(function.analysis, function.capturedVariables)

      refinePoint(analysis.withFunction(ExpressionID(lambda.body), function), point)
    }

    private def refineLetRec(analysis: HeapApproximationAnalysis, point: Point, e: LetRec)(using Symbols): (HeapApproximationAnalysis, Boolean) = {
      val functionsAnalysis = e.fds.foldLeft(analysis) { (analysis, fd) =>
        exprOps.deconstructSpecs(fd.fullBody)._2.fold(analysis) { body =>
          if (analysis.functions.contains(ExpressionID(body))) analysis
          else {
            val function = LocalFunctionAnalysis(fd, refineFunction(fd.params, body, analysis.functions, Set.empty, Map.empty))
            checkReturn(function.analysis, function.params ++ function.capturedVariables, function.body, imported = false)
            checkNoCapturedMutation(function.analysis, function.capturedVariables)

            analysis.withFunction(ExpressionID(body), function)
          }
        }
      }

      refinePoint(functionsAnalysis, point)
    }

    /** The object `e` designates in `heap`, looking through bindings to the expression producing the value. */
    def resolveExpression(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Expr): HeapLocation =
      heap.results(graph.exitOf(e))

    private def refineHeap(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Expr)(using Symbols): HeapPointApproximation = e match {
      case e: Let    => refineLet(graph, heap, e)
      case e: LetVar => refineLetVar(graph, heap, e)
      case _: LetRec => heap

      case e @ WriteBack(_)    => withEmptyResult(heap, e)
      case e: Assignment       => refineAssignment(graph, heap, e)
      case e: FieldAssignment  => refineFieldAssignment(graph, heap, e)
      case e: ArrayUpdate      => refineArrayUpdate(graph, heap, e)
      case e: MutableMapUpdate => refineMutableMapUpdate(graph, heap, e)

      case e: IfExpr => refineIf(graph, heap, e)
      case e: Block  => refineBlock(graph, heap, e)

      case e if !isTrackedType(e) => withEmptyResult(heap, e)

      case e: Variable      => refineVariable(graph, heap, e)
      case e: ClassSelector => refineClassSelector(graph, heap, e)
      case e: TupleSelect   => refineTupleSelect(graph, heap, e)
      case e: ArraySelect   => refineArraySelect(graph, heap, e)

      case e: ClassConstructor => refineClassConstructor(graph, heap, e)
      case e: Tuple            => refineTuple(graph, heap, e)

      case e: FiniteArray  => refineFiniteArray(graph, heap, e)
      case e: LargeArray   => refineLargeArray(graph, heap, e)
      case e: ArrayUpdated => refineArrayUpdated(graph, heap, e)

      case e: MutableMapWithDefault => refineMutableMapWithDefault(graph, heap, e)
      case e: MutableMapUpdated     => refineMutableMapUpdated(graph, heap, e)
      case e: MutableMapApply       => refineMutableMapApply(graph, heap, e)
      case e: MutableMapDuplicate   => refineMutableMapDuplicate(graph, heap, e)

      case e: Annotated    => heap.withExpressionResult(e, resolveExpression(graph, heap, e.body))
      case e: AsInstanceOf => heap.withExpressionResult(e, resolveExpression(graph, heap, e.expr))
      case e: Assert       => heap.withExpressionResult(e, resolveExpression(graph, heap, e.body))
      case e: Assume       => heap.withExpressionResult(e, resolveExpression(graph, heap, e.body))

      case e @ (_: Error | _: Choose) => withEmptyResult(heap, e)
      case e => throw AliasingAssignRewriteException.unsupportedConstruct(e)
    }

    private def refineLet(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Let)(using Symbols): HeapPointApproximation =
      heap.withDeclareVariable(e.vd.id, resolveExpression(graph, heap, e.value)).withoutResults(e.value)

    private def refineLetVar(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: LetVar)(using Symbols): HeapPointApproximation =
      heap.withDeclareVariable(e.vd.id, resolveExpression(graph, heap, e.value)).withoutResults(e.value)

    private def refineAssignment(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Assignment)(using Symbols): HeapPointApproximation =
      withEmptyResult(heap.withAssignVariable(e.v.id, resolveExpression(graph, heap, e.value)).withoutResults(e.value), e)

    private def refineFieldAssignment(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: FieldAssignment)(using Symbols): HeapPointApproximation =
      withEmptyResult(heap.withAssignField(resolveExpression(graph, heap, e.obj), e.selector, resolveExpression(graph, heap, e.value)), e)

    private def refineVariable(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Variable)(using Symbols): HeapPointApproximation = {
      val (location, newHeap) = heap.locate(e, heap.resolveVariable(e.id))
      newHeap.withExpressionResult(e, location)
    }

    private def refineClassSelector(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: ClassSelector)(using Symbols): HeapPointApproximation = {
      val (reference, resolvedHeap) = heap.resolveField(resolveExpression(graph, heap, e.expr), e.selector)
      val (location, newHeap) = resolvedHeap.locate(e, reference)

      newHeap.withExpressionResult(e, location)
    }

    private def refineTupleSelect(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: TupleSelect)(using Symbols): HeapPointApproximation = {
      val (reference, resolvedHeap) = heap.resolveTuple(resolveExpression(graph, heap, e.tuple), e.index)
      val (location, newHeap) = resolvedHeap.locate(e, reference)

      newHeap.withExpressionResult(e, location)
    }

    private def refineArraySelect(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: ArraySelect)(using Symbols): HeapPointApproximation = {
      val collection = resolveExpression(graph, heap, e.array)
      val (elements, resolvedHeap) = withObservedElement(heap, collection, e.index, e).resolveElements(collection, e.index)
      val (location, newHeap) = resolvedHeap.locate(e, elements)

      newHeap.withExpressionResult(e, location)
    }

    private def refineClassConstructor(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: ClassConstructor)(using Symbols): HeapPointApproximation = {
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val fieldsHeap = e.ct.tcd.fields.zip(e.args).foldLeft(allocatedHeap) { case (heap, (vd, arg)) => heap.withAssignField(instance, vd.id, resolveExpression(graph, heap, arg)) }
      val (location, newHeap) = fieldsHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineTuple(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Tuple)(using Symbols): HeapPointApproximation = {
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val componentsHeap = e.exprs.zipWithIndex.foldLeft(allocatedHeap) { case (heap, (component, index)) => heap.withAssignTuple(instance, index + 1, resolveExpression(graph, heap, component)) }
      val (location, newHeap) = componentsHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineFiniteArray(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: FiniteArray)(using Symbols): HeapPointApproximation = {
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val elementsHeap = e.elems.zipWithIndex.foldLeft(allocatedHeap.withCollection(instance)) { case (heap, (element, index)) =>
        heap.withElement(instance, Int32Literal(index), ExactHeapReference(resolveExpression(graph, heap, element)))
      }
      val (location, newHeap) = elementsHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineLargeArray(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: LargeArray)(using Symbols): HeapPointApproximation = {
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val elementsHeap = e.elems.toSeq.foldLeft(allocatedHeap.withCollection(instance)) { case (heap, (index, element)) =>
        heap.withElement(instance, Int32Literal(index), ExactHeapReference(resolveExpression(graph, heap, element)))
      }
      val (location, newHeap) = elementsHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineArrayUpdated(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: ArrayUpdated)(using Symbols): HeapPointApproximation = {
      if (CallResult.isWithin(e.value)) {
        return heap.withExpressionResult(e, resolveExpression(graph, heap, e.array))
      }

      val (instance, allocatedHeap) = heap.withAllocation(e)
      val copiedHeap =
        if (isMutableType(e.value.getType)) allocatedHeap.withCollectionCopy(instance, resolveExpression(graph, heap, e.array), Some(e.index)).withElement(instance, e.index, ExactHeapReference(resolveExpression(graph, heap, e.value)))
        else allocatedHeap.withCollection(instance)
      val (location, newHeap) = copiedHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineArrayUpdate(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: ArrayUpdate)(using Symbols): HeapPointApproximation =
      withEmptyResult(heap.withElement(resolveExpression(graph, heap, e.array), e.index, ExactHeapReference(resolveExpression(graph, heap, e.value))), e)

    private def refineMutableMapWithDefault(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: MutableMapWithDefault)(using Symbols): HeapPointApproximation = {
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val (location, newHeap) = allocatedHeap.withCollection(instance).withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineMutableMapUpdated(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: MutableMapUpdated)(using Symbols): HeapPointApproximation = {
      if (CallResult.isWithin(e.value)) {
        return heap.withExpressionResult(e, resolveExpression(graph, heap, e.map))
      }

      val (instance, allocatedHeap) = heap.withAllocation(e)
      val copiedHeap =
        if (isMutableType(e.value.getType)) allocatedHeap.withCollectionCopy(instance, resolveExpression(graph, heap, e.map), Some(e.key)).withElement(instance, e.key, ExactHeapReference(resolveExpression(graph, heap, e.value)))
        else allocatedHeap.withCollection(instance)
      val (location, newHeap) = copiedHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineMutableMapUpdate(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: MutableMapUpdate)(using Symbols): HeapPointApproximation =
      withEmptyResult(heap.withElement(resolveExpression(graph, heap, e.map), e.key, ExactHeapReference(resolveExpression(graph, heap, e.value))), e)

    private def refineMutableMapApply(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: MutableMapApply)(using Symbols): HeapPointApproximation = {
      val collection = resolveExpression(graph, heap, e.map)
      val (elements, resolvedHeap) = withObservedElement(heap, collection, e.key, e).resolveElements(collection, e.key)
      val (location, newHeap) = resolvedHeap.locate(e, elements)

      newHeap.withExpressionResult(e, location)
    }

    private def refineMutableMapDuplicate(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: MutableMapDuplicate)(using Symbols): HeapPointApproximation = {
      val MutableMapType(_, to) = e.map.getType.getType: @unchecked
      val (instance, allocatedHeap) = heap.withAllocation(e)
      val copiedHeap =
        if (isMutableType(to)) allocatedHeap.withCollectionCopy(instance, resolveExpression(graph, heap, e.map), None)
        else allocatedHeap.withCollection(instance)
      val (location, newHeap) = copiedHeap.withLocation(e, ExactHeapReference(instance))

      newHeap.withExpressionResult(e, location)
    }

    private def refineIf(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: IfExpr)(using Symbols): HeapPointApproximation = {
      val IfExpr(condition: Variable, _, _) = e: @unchecked

      def branchReference(branch: Expr): HeapReference =
        heap.results.get(graph.exitOf(branch)).fold(NoHeapReference: HeapReference)(ExactHeapReference(_))

      val (_, conditionHeap) = heap.withoutResults(e.thenn).withoutResults(e.elze).withVariable(condition.id)
      val (location, newHeap) = conditionHeap.withLocation(e, HeapReference.conditional(conditionOf(graph, condition), branchReference(e.thenn), branchReference(e.elze)))
      newHeap.withExpressionResult(e, location)
    }

    private def conditionOf(graph: HeapApproximationGraph, condition: Variable)(using Symbols): Expr = {
      val assigned = graph.points.values.collect { case Point(_, LetVar(vd, _, _), _) => vd.id }.toSet
      val definition = graph.points.values.collectFirst { case Point(_, Let(vd, value, _), _) if vd.id == condition.id => value }

      definition.filter { value =>
        exprOps.variablesOf(value).forall(variable => !isMutableType(variable.tpe) && !assigned(variable.id)) &&
        !exprOps.exists {
          case _: FunctionInvocation | _: Application | _: ApplyLetRec | _: ClassSelector => true
          case _ => false
        }(value)
      }.getOrElse(condition)
    }

    private def withEmptyResult(heap: HeapPointApproximation, e: Expr): HeapPointApproximation = {
      val (location, newHeap) = heap.withLocation(e, NoHeapReference)
      newHeap.withExpressionResult(e, location)
    }

    private def refineBlock(graph: HeapApproximationGraph, heap: HeapPointApproximation, e: Block)(using Symbols): HeapPointApproximation =
      heap.withoutResults(e).withExpressionResult(e, resolveExpression(graph, heap, e.last)).withExpressionResult(e.last, resolveExpression(graph, heap, e.last))

    private def withObservedElement(heap: HeapPointApproximation, collection: HeapObject, index: Expr, e: Expr)(using Symbols): HeapPointApproximation = {
      if (!isMutableType(e.getType)) {
        return heap
      }

      heap.withObservedElement(collection, index, heap.references(heap.results(ExpressionID(e))))
    }

    private def checkInvariant(analysis: HeapApproximationAnalysis, point: Point)(using Symbols): Unit = point.e match {
      case e: FunctionInvocation => checkDistinctArguments(analysis, point, e.args)
      case e: ApplyLetRec => checkDistinctArguments(analysis, point, e.args)
      case e: Application => checkDistinctArguments(analysis, point, e.args)
      case e: LargeArray => checkFreshDefault(analysis, point, e.default)
      case e: ArraySelect => checkUnshared(analysis, point, Seq(e.array))
      case e: MutableMapApply => checkUnshared(analysis, point, Seq(e.map))
      case e: ArrayUpdate => checkUnshared(analysis, point, Seq(e.array))
      case e: MutableMapUpdate => checkUnshared(analysis, point, Seq(e.map))
      case _ =>
    }

    private def checkDistinctArguments(analysis: HeapApproximationAnalysis, point: Point, args: Seq[Expr])(using Symbols): Unit = {
      checkUnshared(analysis, point, args)

      val heap = parentHeap(analysis, point)
      val reachable = args.filter(arg => isMutableType(arg.getType)).map(arg => heap.resolveReachableTargets(resolveExpression(analysis.graph, heap, arg)))
      val overlapping = reachable.indices.exists(i => reachable.indices.exists(j => i < j && reachable(i).intersect(reachable(j)).targets.nonEmpty))

      if (overlapping || reachable.exists(heap.resolveSharedTargets(_).targets.nonEmpty)) throw AliasingAssignRewriteException.sharedArgument(point.e)
    }

    private def checkFreshDefault(analysis: HeapApproximationAnalysis, point: Point, default: Expr)(using Symbols): Unit = {
      checkUnshared(analysis, point, Seq(default))

      val heap = parentHeap(analysis, point)
      if (isMutableType(default.getType) && !heap.isFresh(resolveExpression(analysis.graph, heap, default))) throw AliasingAssignRewriteException.nonFreshDefault(default)
    }

    private def checkUnshared(analysis: HeapApproximationAnalysis, point: Point, values: Seq[Expr])(using Symbols): Unit = {
      val heap = parentHeap(analysis, point)
      val shared = values.filter(value => isMutableType(value.getType)).find(value => heap.isShared(resolveExpression(analysis.graph, heap, value)))

      shared.foreach(value => throw AliasingAssignRewriteException.sharedCollection(value))
    }

    private def returnedExpressions(body: Expr): Seq[Expr] = {
      def results(e: Expr): Seq[Expr] = e match {
        case Let(_, _, rest) => results(rest)
        case LetVar(_, _, rest) => results(rest)
        case Block(_, last) => results(last)
        case other => Seq(other)
      }

      results(body) ++ exprOps.collect[Expr] {
        case Return(e) => Set(e)
        case _ => Set.empty
      }(body)
    }

    def checkReturn(analysis: HeapApproximationAnalysis, params: Seq[ValDef], body: Expr, imported: Boolean)(using Symbols): Unit = {
      val returnedParameters = analysis.graph.points.values.collect { case Point(_, LetVar(_, Variable(id, _, _), _), _) => id }.toSet
      val readOnly = params.filter(vd => isMutableType(vd.tpe) && !returnedParameters(vd.id))
      val returned = returnedExpressions(body).filter(e => isMutableType(e.getType) && analysis.heapAt.contains(ExpressionID(e)))

      analysis.heapAt.get(analysis.graph.exitpoint).foreach { exitHeap =>
        val readOnlyReachable = readOnly.map(vd => exitHeap.resolveReachableTargets(HeapVariable(vd.id)))

        returned.foreach { result =>
          val location = resolveExpression(analysis.graph, exitHeap, result)
          val reachable = exitHeap.resolveReachableTargets(location)

          if (exitHeap.isShared(location)) throw AliasingAssignRewriteException.nonFreshResult(result)

          if (imported) {
            if (exitHeap.resolveSharedTargets(reachable).targets.exists(target => isInternalSite(analysis.graph, target.instance.site))) throw AliasingAssignRewriteException.nonFreshResult(result)
          } else {
            if (!exitHeap.isDisjoint(location)) throw AliasingAssignRewriteException.nonFreshResult(result)
            if (readOnlyReachable.exists(reachable.intersect(_).targets.nonEmpty)) throw AliasingAssignRewriteException.nonFreshResult(result)
          }
        }
      }
    }

    private def checkNoCapturedMutation(analysis: HeapApproximationAnalysis, captured: Seq[ValDef])(using Symbols): Unit = {
      def mutatedReceiver(e: Expr): Option[Expr] = e match {
        case FieldAssignment(receiver, _, _) => Some(receiver)
        case ArrayUpdate(receiver, _, _) => Some(receiver)
        case MutableMapUpdate(receiver, _, _) => Some(receiver)
        case assignment: Assignment => WriteBack.unapply(assignment)
        case _ => None
      }

      def mutatedTargets(heap: HeapPointApproximation, e: Expr, receiver: Expr): HeapTargetSet = e match {
        case _: FieldAssignment | _: ArrayUpdate | _: MutableMapUpdate => heap.resolveTargets(resolveExpression(analysis.graph, heap, receiver))
        case _ => heap.resolveReachableTargets(resolveExpression(analysis.graph, heap, receiver))
      }

      val capturedIdentifiers = captured.map(_.id).toSet

      analysis.graph.points.values.foreach { point =>
        point.e match {
          case Assignment(variable, _) if capturedIdentifiers(variable.id) && isMutableType(variable.tpe) => throw AliasingAssignRewriteException.capturedMutation(point.e)
          case _ =>
        }

        for {
          heap <- analysis.heapAt.get(point.id)
          receiver <- mutatedReceiver(point.e)
        } {
          val capturedReachable = captured.filter(vd => isMutableType(vd.tpe)).map(vd => heap.resolveReachableTargets(HeapVariable(vd.id)))
          if (capturedReachable.exists(captured => mutatedTargets(heap, point.e, receiver).intersect(captured).targets.nonEmpty)) throw AliasingAssignRewriteException.capturedMutation(point.e)
        }
      }
    }

    private def isMutableType(tpe: Type)(using symbols: Symbols): Boolean = symbols.isMutableType(tpe)

    private def checkInstantiation(e: Expr, tpe: Type)(using Symbols): Unit = {
      val instantiations = tpe match {
        case ct: ClassType => ct.tcd.cd.tparams.zip(ct.tps)
        case adt: ADTType => adt.getSort.definition.tparams.zip(adt.tps)
        case _ => Seq.empty
      }

      instantiations.foreach { case (tdef, instance) =>
        if (isMutableType(instance) && !tdef.flags.contains(IsMutable)) {
          throw AliasingAssignRewriteException.mutableInstantiation(e)
        }
      }

      val untracked = tpe match {
        case SetType(element) => Seq(element)
        case BagType(element) => Seq(element)
        case MapType(from, _) => Seq(from)
        case MutableMapType(from, _) => Seq(from)
        case _ => Seq.empty
      }

      if (untracked.exists(isMutableType)) {
        throw AliasingAssignRewriteException.mutableInstantiation(e)
      }

      tpe match {
        case NAryType(tps, _) => tps.foreach(checkInstantiation(e, _))
        case _ =>
      }
    }

    private def isTrackedType(e: Expr)(using Symbols): Boolean = {
      checkInstantiation(e, e.getType)
      isMutableType(e.getType)
    }
  }
}
