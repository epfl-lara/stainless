/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait HeapApproximationPoints extends HeapApproximations {
  import s._

  case class HeapPointApproximation(
    scope: Int,
    
    objects: Map[HeapObject, HeapScopedObject],
    
    references: HeapReferences,
    results: Map[ExpressionID, HeapLocation]
  ) {
    def withDeclareVariable(identifier: Identifier, location: HeapAddress): HeapPointApproximation = {
      val variable = HeapVariable(identifier)

      withObject(variable).copy(references = references.updated(variable, ExactHeapReference(location)))
    }

    def withAssignVariable(identifier: Identifier, location: HeapAddress): HeapPointApproximation = {
      val variable = HeapVariable(identifier)
      if (!isAlive(variable)) {
        throw new IllegalStateException(s"$variable is assigned but not declared")
      }

      copy(references = references.updated(variable, ExactHeapReference(location)))
    }

    def withReference(source: HeapObject, reference: HeapReference): HeapPointApproximation =
      withObject(source).copy(references = references.updated(source, reference))

    def embed(instance: HeapObject, structure: HeapObjectStructure): Option[(HeapObjectRepresentation, HeapPointApproximation)] =
      structure.children.foldLeft(Option((HeapObjectRepresentation(instance, Map.empty), this))) { case (embedded, (accessor, child)) =>
        embedded.flatMap { case (representation, heap) =>
          val (reference, resolvedHeap) = accessor match {
            case FieldAccessor(identifier) => heap.resolveField(instance, identifier)
            case TupleAccessor(index) => heap.resolveTuple(instance, index)
            case ElementAccessor(_) => throw new IllegalArgumentException(s"$accessor cannot be embedded")
          }
          val targets = resolvedHeap.deref(reference).toSet()

          val children = targets.foldLeft(Option.when(targets.nonEmpty)((Set.empty[HeapObjectRepresentation], resolvedHeap))) { case (children, target) =>
            children.flatMap { case (children, heap) => heap.embed(target, child).map { case (embedded, embeddedHeap) => (children + embedded, embeddedHeap) } }
          }

          children.map { case (children, childrenHeap) => (representation.copy(children = representation.children + (accessor -> children)), childrenHeap) }
        }
      }

    def withVariable(identifier: Identifier): (HeapVariable, HeapPointApproximation) = {
      val variable = HeapVariable(identifier)
      (variable, withObject(variable))
    }

    /** What variable `identifier` currently points to. */
    def resolveVariable(identifier: Identifier): HeapReference =
      references(HeapVariable(identifier))

    /** `receiver.identifier = value`: writes `location`, the location of `value`, into field `identifier` of every object `receiver` resolves to (strong update). */
    def withAssignField(receiver: HeapObject, identifier: Identifier, location: HeapAddress): HeapPointApproximation = {
      val owners = deref(ExactHeapReference(receiver))

      references.resolve(receiver).foldLeft(this) { (heap, owner) =>
        val target = HeapInstanceField(owner, identifier)
        val previous = heap.references(target)

        heap.withObject(target).copy(references = heap.references.updated(target, owners.mapLeaves(previous)(candidate => if (candidate == owner) ExactHeapReference(location) else previous)))
      }
    }

    /** What field `identifier` of every object `owner` resolves to currently points to. */
    def resolveField(owner: HeapObject, identifier: Identifier): (HeapReference, HeapPointApproximation) = {
      val resolvedHeap = references.resolve(owner).foldLeft(this) { (heap, resolved) =>
        val target = HeapInstanceField(resolved, identifier)
        heap.withObject(target).withResolution(target)
      }
      val reference = resolvedHeap.deref(ExactHeapReference(owner)).mapLeaves(NoHeapReference)(instance => resolvedHeap.references(HeapInstanceField(instance, identifier)))

      (reference, resolvedHeap)
    }

    /** Writes `location`, the location of `value`, into component `index` (1-based) of every tuple `receiver` resolves to (strong update). */
    def withAssignTuple(receiver: HeapObject, index: Int, location: HeapAddress): HeapPointApproximation = {
      val owners = deref(ExactHeapReference(receiver))

      references.resolve(receiver).foldLeft(this) { (heap, owner) =>
        val target = HeapTupleField(owner, index)
        val previous = heap.references(target)

        heap.withObject(target).copy(references = heap.references.updated(target, owners.mapLeaves(previous)(candidate => if (candidate == owner) ExactHeapReference(location) else previous)))
      }
    }

    /** What component `index` (1-based) of every tuple `owner` resolves to currently points to. */
    def resolveTuple(owner: HeapObject, index: Int): (HeapReference, HeapPointApproximation) = {
      val resolvedHeap = references.resolve(owner).foldLeft(this) { (heap, resolved) =>
        val target = HeapTupleField(resolved, index)
        heap.withObject(target).withResolution(target)
      }
      val reference = resolvedHeap.deref(ExactHeapReference(owner)).mapLeaves(NoHeapReference)(instance => resolvedHeap.references(HeapTupleField(instance, index)))

      (reference, resolvedHeap)
    }

    def withCollection(head: HeapInstance): HeapPointApproximation = {
      val elements = HeapElements(head)

      withObject(elements).copy(references = references.updated(head, ExactHeapReference(elements)))
    }

    def withCollectionCopy(head: HeapInstance, source: HeapObject, written: Option[Expr]): HeapPointApproximation = {
      val copiedHeap = withCollection(head)
      val sources = heads(source)
      val shared = sources.foldLeft(copiedHeap.references(head))((shared, sourceHead) => shared.union(references(sourceHead)))
      val sharedHeap = copiedHeap.copy(references = (sources + head).foldLeft(copiedHeap.references)(_.updated(_, shared)))
      val slots = sources.flatMap(sourceHead => objects(HeapElements(sourceHead)).children).collect { case slot: HeapElement if !written.contains(slot.index) => slot }

      slots.foldLeft(sharedHeap) { (heap, slot) =>
        val copy = HeapElement(HeapElements(head), slot.index)
        val copyHeap = heap.withObject(copy)

        copyHeap.copy(references = copyHeap.references.updated(copy, copyHeap.references(copy).union(heap.references(slot))))
      }
    }

    def withUnsharedElements: HeapPointApproximation = {
      val alone = objects.keySet.collect { case head: HeapInstance => head }.filter { head =>
        val shared = references(head).toSet()
        shared.size > 1 && shared.forall(elements => holdersOf(elements) == Set(head))
      }

      copy(references = alone.foldLeft(references)((references, head) => references.updated(head, ExactHeapReference(HeapElements(head)))))
    }

    def isShared(source: HeapObject): Boolean =
      resolveReachableTargets(source).targets.exists(target => references(target.instance).toSet().size > 1)

    def withElement(collection: HeapObject, index: Expr, element: HeapReference): HeapPointApproximation = {
      val collectionHeads = deref(ExactHeapReference(collection))

      heads(collection).foldLeft(this) { (heap, head) =>
        val slot = HeapElement(HeapElements(head), index)
        val slotHeap = heap.withObject(slot)
        val previous = slotHeap.references(slot)

        slotHeap.copy(references = slotHeap.references.updated(slot, collectionHeads.mapLeaves(previous)(candidate => if (candidate == head) element else previous)))
      }
    }

    def iterationElements(entry: HeapPointApproximation): Set[HeapElement] =
      objects.keySet.collect { case slot: HeapElement if !entry.isAlive(slot) => slot }

    def withoutElements(slots: Set[HeapElement]): HeapPointApproximation = {
      val removed = slots.map(slot => slot: HeapObject)

      copy(
        objects = (objects -- removed).map { case (heapObject, scoped) => heapObject -> scoped.copy(children = scoped.children -- removed) },
        references = references.prune(removed)
      )
    }

    def withObservedElement(collection: HeapObject, index: Expr, original: HeapReference): HeapPointApproximation = {
      def observed(reference: HeapReference): HeapReference = reference match {
        case NoHeapReference => original
        case ConditionalHeapReference(condition, thenn, elze) => HeapReference.conditional(condition, observed(thenn), observed(elze))
        case other => other
      }

      val collectionHeads = deref(ExactHeapReference(collection))

      heads(collection).foldLeft(this) { (heap, head) =>
        val slot = HeapElement(HeapElements(head), index)
        val slotHeap = heap.withObject(slot)
        val previous = slotHeap.references(slot)

        slotHeap.copy(references = slotHeap.references.updated(slot, collectionHeads.mapLeaves(previous)(candidate => if (candidate == head) observed(previous) else previous)))
      }
    }

    def resolveElements(collection: HeapObject, index: Expr): (HeapReference, HeapPointApproximation) = {
      val slots = heads(collection).flatMap(head => objects(HeapElements(head)).children)
      val resolvedHeap = slots.foldLeft(this)(_.withResolution(_))
      val reference = resolvedHeap.deref(ExactHeapReference(collection)).mapLeaves(NoHeapReference) {
        case head: HeapInstance => resolvedHeap.references(HeapElement(HeapElements(head), index))
        case other => throw new IllegalStateException(s"$other is not a collection")
      }

      (reference, resolvedHeap)
    }

    def boundIndices(collection: HeapObject): Set[Expr] =
      heads(collection).flatMap(head => objects(HeapElements(head)).children).collect { case slot: HeapElement if isBound(slot) => slot.index }

    /** The instance allocated by `e`. */
    def withAllocation(e: Expr): (HeapInstance, HeapPointApproximation) =
      withAllocation(ExpressionID(e))

    def withAllocation(site: ExpressionID): (HeapInstance, HeapPointApproximation) = {
      val instance = HeapInstance(site)
      (instance, withObject(instance))
    }

    /** The location keyed by `e`, pointing to `reference` (strong update). */
    def withLocation(e: Expr, reference: HeapReference): (HeapLocation, HeapPointApproximation) =
      withLocation(ExpressionID(e), reference)

    def withLocation(site: ExpressionID, reference: HeapReference): (HeapLocation, HeapPointApproximation) = {
      val location = HeapLocation(site)
      (location, withObject(location).copy(references = references.updated(location, reference)))
    }

    def withRecursiveLocation(recursive: HeapRecursiveAddress): (HeapRecursiveAddress, HeapPointApproximation) =
      (recursive, withObject(recursive))

    /** The location `reference` designates when it is exactly one location, otherwise the location keyed by `e`, pointing to `reference`. */
    def locate(e: Expr, reference: HeapReference): (HeapLocation, HeapPointApproximation) = reference match {
      case ExactHeapReference(location: HeapLocation) => (location, this)
      case _ => withLocation(e, reference)
    }

    def withExpressionResult(target: Expr, location: HeapLocation): HeapPointApproximation =
      copy(results = results + (ExpressionID(target) -> location))

    def withoutResults(e: Expr): HeapPointApproximation =
      copy(results = results -- exprOps.collect[ExpressionID](inner => Set(ExpressionID(inner)))(e))

    def collect(identifiers: Set[Identifier]): HeapPointApproximation = {
      val variables = identifiers.map(identifier => HeapVariable(identifier): HeapObject)

      copy(references = variables.foldLeft(references)((references, variable) => references.updated(variable, NoHeapReference)))
    }

    def prune(scope: Int): HeapPointApproximation = {
      def reachFrom(visited: Set[HeapObject], heapObject: HeapObject): Set[HeapObject] = {
        if (visited(heapObject)) {
          return visited
        }

        val children = objects.get(heapObject).fold(Set.empty[HeapObject])(_.children)

        (references(heapObject).toSet() ++ children).foldLeft(visited + heapObject)(reachFrom)
      }

      val variables = objects.collect { case (variable: HeapVariable, scoped) if scoped.scope <= scope => variable }.toSet
      val reachable = (variables ++ results.values).foldLeft(Set.empty[HeapObject])(reachFrom)

      val pruned = objects.keySet -- reachable

      copy(scope = scope, objects = objects -- pruned, references = references.prune(pruned))
    }

    def isAlive(heapObject: HeapObject): Boolean = objects.contains(heapObject)

    def isEmpty: Boolean = objects.isEmpty

    def merge(other: HeapPointApproximation): HeapPointApproximation = {
      if (isEmpty) {
        return other
      }

      if (other.isEmpty) {
        return this
      }

      copy(
        objects = mergeObjects(other.objects),
        references = references.combine(other.references)(_.union(_)),
        results = results ++ other.results
      )
    }

    /** Joins the heaps of the two branches of an `if` on `condition`: registries and results are merged, references that differ become conditional on `condition`. */
    def mergeConditional(condition: Expr, elze: HeapPointApproximation): HeapPointApproximation = {
      if (isEmpty) {
        return elze
      }

      if (elze.isEmpty) {
        return this
      }

      val mergedHeap = copy(objects = mergeObjects(elze.objects))
      val registeredHeap = exprOps.variablesOf(condition).foldLeft(mergedHeap)((heap, variable) => heap.withObject(HeapVariable(variable.id)))

      registeredHeap.copy(
        references = references.combine(elze.references)(HeapReference.conditional(condition, _, _)),
        results = results ++ elze.results
      )
    }

    def resolveTargets(source: HeapObject): HeapTargetSet = {
      def resolveObject(target: HeapObject, choices: Seq[(Expr, Boolean)], visited: Set[HeapObject]): Seq[HeapTarget] = target match {
        case instance: HeapInstance => Seq(HeapTarget(Set(HeapTargetCondition(choices)), instance))
        case _ if visited(target) => Seq.empty
        case _ => resolveReference(references(target), choices, visited + target)
      }

      def resolveReference(reference: HeapReference, choices: Seq[(Expr, Boolean)], visited: Set[HeapObject]): Seq[HeapTarget] = reference match {
        case NoHeapReference => Seq.empty
        case ExactHeapReference(target) => resolveObject(target, choices, visited)
        case AmbiguousHeapReference(targets) => targets.toSeq.flatMap(resolveObject(_, choices, visited))
        case ConditionalHeapReference(condition, thenn, elze) => resolveReference(thenn, choices :+ (condition -> true), visited) ++ resolveReference(elze, choices :+ (condition -> false), visited)
      }

      HeapTargetSet.from(resolveObject(source, Seq.empty, Set.empty))
    }

    def resolveDependencies(targets: HeapTargetSet): HeapTargetDependencySet = {
      def dependenciesOf(target: HeapTarget, accessors: Seq[HeapAccessor], targets: Seq[HeapTargetSet], visiting: Set[HeapInstance]): Set[HeapTargetDependency] =
        holdersOf(target.instance).flatMap(holder => dependenciesOfHolder(target, holder, accessors, targets, visiting))

      def dependenciesOfHolder(target: HeapTarget, holder: HeapObject, accessors: Seq[HeapAccessor], targets: Seq[HeapTargetSet], visiting: Set[HeapInstance]): Set[HeapTargetDependency] = {
        val holderTargets = resolveTargets(holder)
        val condition = HeapTargetCondition.and(target.conditions, holderTargets.conditionsOf(target.instance))

        if (condition.isEmpty) {
          return Set.empty
        }

        def dependenciesOfOwner(owner: HeapObject, accessor: HeapAccessor): Set[HeapTargetDependency] = owner match {
          case owner: HeapInstance if !visiting(owner) => dependenciesOf(HeapTarget(condition, owner), accessor +: accessors, holderTargets +: targets, visiting + target.instance)
          case _ => Set.empty
        }

        holder match {
          case HeapVariable(identifier) => Set(HeapTargetDependency(condition, identifier, accessors, holderTargets +: targets))
          case HeapInstanceField(owner, identifier) => dependenciesOfOwner(owner, FieldAccessor(identifier))
          case HeapTupleField(owner, index) => dependenciesOfOwner(owner, TupleAccessor(index))
          case HeapElement(elements, index) => dependenciesOfOwner(elements.owner, ElementAccessor(index))
          case _ => Set.empty
        }
      }

      targets.targets.flatMap(target => dependenciesOf(target, Seq.empty, Seq.empty, Set.empty))
    }

    def resolveReachableTargets(source: HeapObject): HeapTargetSet = {
      def reachFrom(target: HeapTarget, visiting: Set[HeapInstance]): Set[HeapTarget] = {
        if (visiting(target.instance)) {
          return Set.empty
        }

        val children = holdersWithin(target.instance).flatMap(holder => resolveTargets(holder).targets)
          .map(child => child.withConditions(HeapTargetCondition.and(target.conditions, child.conditions)))

        children.filter(_.conditions.nonEmpty).flatMap(child => reachFrom(child, visiting + target.instance)).toSet + target
      }

      val reachable = resolveTargets(source).targets.flatMap(reachFrom(_, Set.empty))

      HeapTargetSet.from(reachable)
    }

    def resolveSharedTargets(targets: HeapTargetSet): HeapTargetSet = {
      val shared = targets.targets.toSeq.flatMap { target =>
        val holderTargets = holdersWithin(target.instance).map(resolveReachableTargets)
        val cycles = holderTargets.flatMap(_.targets.filter(_.instance == target.instance))
        val overlaps = for {
          i <- holderTargets.indices
          j <- holderTargets.indices
          if i < j
          overlap <- holderTargets(i).intersect(holderTargets(j)).targets
        } yield overlap

        (cycles ++ overlaps).map(overlap => overlap.withConditions(HeapTargetCondition.and(target.conditions, overlap.conditions))).filter(_.conditions.nonEmpty)
      }

      HeapTargetSet.from(shared)
    }

    def represent(target: HeapObject): HeapObjectRepresentation = {
      def representFrom(target: HeapObject, visited: Set[HeapObject]): HeapObjectRepresentation = target match {
        case instance: HeapInstance if !visited(instance) =>
          val children = holdersWithin(instance).map { holder =>
            accessorOf(holder) -> deref(references(holder)).toSet().map(representFrom(_, visited + instance))
          }

          HeapObjectRepresentation(instance, children.toMap)

        case _ => HeapObjectRepresentation(target, Map.empty)
      }

      representFrom(target, Set.empty)
    }

    def isDisjoint(source: HeapObject): Boolean =
      resolveSharedTargets(resolveReachableTargets(source)).targets.isEmpty

    def isFresh(source: HeapObject): Boolean =
      deref(references(source)).toSet().forall { target =>
        val owned = objectsOf(represent(target))

        owned.forall(holdersOutside(_, owned).forall(_ == source))
      }

    /** `reference` with every location replaced by what it points to. */
    private def deref(reference: HeapReference): HeapReference = reference match {
      case ExactHeapReference(location: HeapAddress) =>
        deref(references(location))

      case AmbiguousHeapReference(targets) =>
        targets.foldLeft(NoHeapReference: HeapReference)((result, target) => result.union(deref(ExactHeapReference(target))))

      case ConditionalHeapReference(condition, thenn, elze) =>
        HeapReference.conditional(condition, deref(thenn), deref(elze))

      case _ =>
        reference
    }

    private def objectsOf(representation: HeapObjectRepresentation): Set[HeapObject] =
      representation.children.values.flatten.foldLeft(Set(representation.instance))(_ ++ objectsOf(_))

    private def holdersOutside(target: HeapObject, owned: Set[HeapObject]): Set[HeapObject] =
      holdersOf(target).filter {
        case HeapInstanceField(owner, _) => !owned(owner)
        case HeapTupleField(owner, _) => !owned(owner)
        case HeapElement(elements, _) => !owned(elements.owner)
        case _ => true
      }

    private def isBound(slot: HeapElement): Boolean = {
      val owned = objectsOf(represent(slot.elements.owner))

      deref(references(slot)).toSet().flatMap(target => objectsOf(represent(target))).exists(holdersOutside(_, owned).nonEmpty)
    }

    private def holdersOf(target: HeapObject): Set[HeapObject] = {
      def holdersFrom(node: HeapObject, visited: Set[HeapObject]): Set[HeapObject] =
        references.parentsOf(node).flatMap {
          case location: HeapAddress if visited(location) => Set.empty
          case location: HeapAddress => holdersFrom(location, visited + location)
          case holder => Set(holder)
        }

      holdersFrom(target, Set.empty)
    }

    private def accessorOf(holder: HeapObject): HeapAccessor = holder match {
      case HeapInstanceField(_, identifier) => FieldAccessor(identifier)
      case HeapTupleField(_, index) => TupleAccessor(index)
      case HeapElement(_, index) => ElementAccessor(index)
      case other => throw new IllegalStateException(s"$other is not a component")
    }

    private def holdersWithin(instance: HeapInstance): Seq[HeapObject] =
      objects(instance).children.toSeq.flatMap {
        case elements: HeapElements => objects(elements).children.toSeq
        case child => Seq(child)
      }

    private def heads(collection: HeapObject): Set[HeapInstance] =
      deref(ExactHeapReference(collection)).toSet().map {
        case head: HeapInstance => head
        case other => throw new IllegalStateException(s"$other is not a collection")
      }

    private def withResolution(holder: HeapObject): HeapPointApproximation =
      references(holder).toSet().foldLeft(this) {
        case (heap, recursive: HeapRecursiveAddress) if heap.references(recursive) != recursive.representation._1 =>
          val (reference, representation) = recursive.representation
          val mergedHeap = heap.merge(representation)

          mergedHeap.copy(references = mergedHeap.references.updated(recursive, reference))

        case (heap, _) => heap
      }

    private def withObject(heapObject: HeapObject): HeapPointApproximation = {
      if (objects.contains(heapObject)) {
        return this
      }

      val registered = objects + (heapObject -> HeapScopedObject(scope, heapObject))

      parentOf(heapObject).fold(copy(objects = registered)) { parent =>
        val scopedParent = registered.getOrElse(parent, throw new IllegalStateException(s"the owner of $heapObject is not registered"))
        copy(objects = registered + (parent -> scopedParent.copy(children = scopedParent.children + heapObject)))
      }
    }

    private def parentOf(heapObject: HeapObject): Option[HeapObject] = heapObject match {
      case HeapInstanceField(owner, _) => Some(owner)
      case HeapTupleField(owner, _) => Some(owner)
      case HeapElements(owner) => Some(owner)
      case HeapElement(elements, _) => Some(elements)
      case _ => None
    }

    private def mergeObjects(other: Map[HeapObject, HeapScopedObject]): Map[HeapObject, HeapScopedObject] =
      other.foldLeft(objects) { case (merged, (key, scoped)) =>
        merged.updatedWith(key) {
          case Some(existing) => Some(existing.copy(children = existing.children ++ scoped.children))
          case None => Some(scoped)
        }
      }
  }

  object HeapPointApproximation {
    def empty(scope: Int): HeapPointApproximation = HeapPointApproximation(scope, Map.empty, HeapReferences.empty, Map.empty)
  }
}
