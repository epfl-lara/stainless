/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.annotation.tailrec
import scala.reflect.ClassTag

trait HeapApproximationPoints extends HeapApproximations {
  import s._

  case class HeapPointApproximation(
    scope: Int,
    objects: Map[HeapObject, HeapScopedObject],
    references: HeapReferences,
    results: Map[ExpressionID, HeapLocation]
  ) {
    /** Whether nothing is registered. */
    def isEmpty: Boolean = objects.isEmpty

    /** Whether `heapObject` is registered. */
    def isAlive(heapObject: HeapObject): Boolean = objects.contains(heapObject)

    /** The registered variables. */
    def variables: Set[HeapVariable] =
      objects.keySet.collect { case variable: HeapVariable => variable }

    /** The values `holder` resolves to, all of kind `T`. */
    def resolveValues[T <: HeapValue](holder: HeapObject)(using tag: ClassTag[T]): Set[T] =
      references.resolve(holder).collect {
        case value: T => value
        case value: HeapValue => throw new IllegalStateException(s"$value is not a ${tag.runtimeClass.getSimpleName}")
      }

    /** The slots of `value` that the heap knows about: its fields, tuple components or elements. */
    def resolveSlots(value: HeapValue): Seq[HeapSlot] =
      children(value).toSeq
        .flatMap {
          case elements: HeapElements => children(elements).toSeq
          case child => Seq(child)
        }
        .collect { case slot: HeapSlot => slot }

    /** The objects registered under each object: slots under their owner or element set, element sets under their collection. */
    private lazy val children: Map[HeapObject, Set[HeapObject]] =
      objects.keySet.toSeq
        .collect {
          case slot: HeapSlot => slot.parent -> (slot: HeapObject)
          case elements: HeapElements => (elements.owner: HeapObject) -> (elements: HeapObject)
        }
        .groupMap(_._1)(_._2)
        .map { case (parent, children) => parent -> children.toSet }
        .withDefaultValue(Set.empty)

    /** Registers `heapObject` at the current scope. */
    private def withObject(heapObject: HeapObject): HeapPointApproximation = {
      if (isAlive(heapObject)) {
        return this
      }

      copy(objects = objects + (heapObject -> HeapScopedObject(scope, heapObject)))
    }

    /** Registers the instance created at `site`. */
    def withInstance(site: ExpressionID): (HeapInstance, HeapPointApproximation) = {
      val instance = HeapInstance(site)

      (instance, withObject(instance))
    }

    /** Registers the tuple created at `site`. */
    def withTuple(site: ExpressionID): (HeapTuple, HeapPointApproximation) = {
      val tuple = HeapTuple(site)

      (tuple, withObject(tuple))
    }

    /** Registers the collection created by `e`. */
    def withCollection(e: Expr): (HeapCollection, HeapPointApproximation) =
      withCollection(ExpressionID(e))

    /** Registers the collection created at `site`, with its own element set. */
    def withCollection(site: ExpressionID): (HeapCollection, HeapPointApproximation) = {
      val collection = HeapCollection(site)
      val registeredHeap = withObject(collection).withObject(collection.elements)

      (collection, registeredHeap.withReference(collection, ExactHeapReference(collection.elements)))
    }

    /** Registers the immutable value written at `site`. */
    def withImmutable(site: ExpressionID): (HeapImmutable, HeapPointApproximation) = {
      val immutable = HeapImmutable(site)

      (immutable, withObject(immutable))
    }

    /** Registers the value created at `site`, of the kind given by `tpe`. */
    def withValue(site: ExpressionID, tpe: Type)(using Symbols): (HeapValue, HeapPointApproximation) = {
      val value = HeapValue(site, tpe)

      (value, withValue(value))
    }

    /** Registers `value`, unless it is a collection already alive. */
    def withValue(value: HeapValue): HeapPointApproximation = value match {
      case instance: HeapInstance => withInstance(instance.site)._2
      case tuple: HeapTuple => withTuple(tuple.site)._2
      case collection: HeapCollection if isAlive(collection) => this
      case collection: HeapCollection => withCollection(collection.site)._2
    }

    /** Declares a variable pointing to `reference`. */
    def withDeclareVariable(identifier: Identifier, reference: HeapReference): HeapPointApproximation = {
      val variable = HeapVariable(identifier)

      withObject(variable)
        .withReference(variable, reference)
    }

    /** Makes a declared variable point to `reference`. */
    def withAssignVariable(identifier: Identifier, reference: HeapReference): HeapPointApproximation =
      withReference(HeapVariable(identifier), reference)

    /** Declares a variable again, at the current scope, pointing to `reference`. */
    def withReassignVariable(identifier: Identifier, reference: HeapReference): HeapPointApproximation =
      withoutObject(Seq(HeapVariable(identifier)))
        .withDeclareVariable(identifier, reference)

    /** What a variable points to. */
    def resolveVariable(identifier: Identifier): HeapReference =
      references(HeapVariable(identifier))

    /** Keeps the variables in `identifiers`, and the other variables and pending results connected to their objects, all at the current scope. */
    def withRestriction(identifiers: Set[Identifier]): HeapPointApproximation = {
      @tailrec
      def connect(kept: Set[HeapObject], shared: Set[HeapValue], others: Set[HeapObject]): (Set[HeapObject], Set[HeapObject]) = {
        val (aliases, outside) = others.partition(other => resolveAllTargets(other).values.exists(shared))

        if (aliases.isEmpty) {
          return (kept, outside)
        }

        connect(kept ++ aliases, shared ++ aliases.flatMap(resolveAllTargets(_).values), outside)
      }

      val (parameters, others) = variables.partition(variable => identifiers(variable.identifier))
      val candidates: Set[HeapObject] = others ++ results.values
      val (kept, outside) = connect(parameters.toSet, parameters.flatMap(resolveAllTargets(_).values), candidates)
      val rescoped = kept
        .collect { case variable: HeapVariable => variable }
        .foldLeft(objects)((objects, variable) => objects.updated(variable, HeapScopedObject(scope, variable)))
      val keptResults = results.filter { case (_, location) => kept(location) }

      copy(objects = rescoped, results = keptResults)
        .withoutObject(outside.collect { case variable: HeapVariable => variable })
        .prune(scope)
    }

    /** Makes the variables `identifiers` point to nothing, keeping them declared. */
    def withoutReferencesOf(identifiers: Set[Identifier]): HeapPointApproximation =
      identifiers.foldLeft(this)((heap, identifier) => heap.withReference(HeapVariable(identifier), NoHeapReference))

    /** Makes `source` point to `reference`, registering it first when it is a slot or an original. */
    def withReference(source: HeapObject, reference: HeapReference): HeapPointApproximation = {
      def withSlot(slot: HeapSlot): HeapPointApproximation = {
        if (isAlive(slot)) {
          return this
        }

        if (!isAlive(slot.parent)) {
          throw new IllegalStateException(s"the owner of $slot is not registered")
        }

        withObject(slot)
      }

      val registered = source match {
        case slot: HeapSlot => withSlot(slot)
        case original: HeapOriginal => withObject(original)
        case _ if isAlive(source) => this
        case _ => throw new IllegalStateException(s"$source is updated but not registered")
      }

      registered.copy(references = registered.references.updated(source, reference))
    }

    /** Makes a field of `owner` point to `reference`. */
    def withAssignField(owner: HeapInstance, identifier: Identifier, reference: HeapReference): HeapPointApproximation =
      withReference(owner.resolveSlot(FieldAccessor(identifier)), reference)

    /** Makes a component of `owner` point to `reference`. */
    def withAssignTuple(owner: HeapTuple, index: Int, reference: HeapReference): HeapPointApproximation =
      withReference(owner.resolveSlot(TupleAccessor(index)), reference)

    /** Makes an element of `head` point to `reference`. */
    def withAssignElement(head: HeapCollection, index: Expr, reference: HeapReference): HeapPointApproximation =
      withReference(head.resolveSlot(ElementAccessor(index)), reference)

    /** Unregisters `heapObjects` and drops their references. */
    def withoutObject(heapObjects: Iterable[HeapObject]): HeapPointApproximation = {
      val removed = heapObjects.toSet

      copy(objects = objects -- removed, references = references.prune(removed))
    }

    /** Records `reference` as the result of `target`, through a location unless it already is one. */
    def withExpressionResult(target: Expr, reference: HeapReference): HeapPointApproximation = {
      val site = ExpressionID(target)

      reference match {
        case ExactHeapReference(location: HeapLocation) =>
          copy(results = results + (site -> location))

        case _ =>
          val location = HeapLocation(site)

          withObject(location)
            .withReference(location, reference)
            .copy(results = results + (site -> location))
      }
    }

    /** What the result recorded at `site` points to. */
    def resolveResult(site: ExpressionID): HeapReference =
      results
        .get(site)
        .fold(NoHeapReference: HeapReference)(location => dereference(ExactHeapReference(location)))

    /** Forgets the results recorded at `sites`. */
    def withoutResults(sites: Set[ExpressionID]): HeapPointApproximation =
      copy(results = results -- sites)

    /** Forgets the results recorded for `e` and its subexpressions. */
    def withoutResults(e: Expr): HeapPointApproximation = {
      val removed = exprOps.collect[ExpressionID](inner => Set(ExpressionID(inner)))(e)

      copy(results = results -- removed)
    }

    /** The same heap, at `scope`. */
    def withScope(scope: Int): HeapPointApproximation =
      copy(scope = scope)

    /** Every object kept alive by the variables in scope and the pending expression results. */
    private lazy val liveObjects: Set[HeapObject] = {
      def reachFrom(visited: Set[HeapObject], heapObject: HeapObject): Set[HeapObject] = {
        if (visited(heapObject)) {
          return visited
        }

        (references(heapObject).toSet ++ children(heapObject)).foldLeft(visited + heapObject)(reachFrom)
      }

      val roots = variables.filter(variable => objects(variable).scope <= scope) ++ results.values

      roots.foldLeft(Set.empty[HeapObject])(reachFrom)
    }

    /** The objects nothing keeps alive anymore, variables out of scope included. */
    private lazy val deadObjects: Set[HeapObject] = objects.keySet -- liveObjects

    /** The heap in canonical form: collections that no longer share their elements get back a single element set, and values only reachable through one holder that does not tell them apart become one value. */
    private def normalize: HeapPointApproximation = {
      def normalizeCollection(heap: HeapPointApproximation, head: HeapCollection): HeapPointApproximation = {
        val own = heap.resolveSlots(head).map(_.accessor).toSet
        val others = (heap.references(head).toSet - head.elements).collect { case elements: HeapElements => elements }
        val (overridden, moved) = others
          .flatMap(elements => heap.resolveSlots(elements.owner))
          .collect { case slot: HeapElement => slot }
          .partition(slot => own(slot.accessor))

        val renaming: Map[HeapObject, HeapObject] =
          moved.map(slot => (slot: HeapObject) -> (head.resolveSlot(slot.accessor): HeapObject)).toMap ++
          others.map(elements => (elements: HeapObject) -> (head.elements: HeapObject))

        heap
          .withoutObject(overridden)
          .renamed(renaming)
      }

      val unshared = objects.keySet
        .collect { case head: HeapCollection => head }
        .filter { head =>
          val elements = references(head).toSet

          elements.size > 1 && elements.forall(references.parentsOf(_) == Set(head))
        }

      def mergeTargets(heap: HeapPointApproximation, holder: HeapObject): HeapPointApproximation = {
        if (holder.isInstanceOf[HeapOriginal]) {
          return heap
        }

        val targets = heap.references(holder) match {
          case AmbiguousHeapReference(references) => references
          case _ => Set.empty[HeapObject]
        }
        val values = targets.collect { case value: HeapValue => value }

        if (values.size < 2 || values.size != targets.size) {
          return heap
        }

        val own: Set[HeapObject] = holder match {
          case slot: HeapSlot => Set(slot, HeapOriginal(slot))
          case _ => Set(holder)
        }

        if (!values.forall(value => heap.references.parentsOf(value).subsetOf(own))) {
          return heap
        }

        val region: Set[HeapValue] = heap.resolveAllTargets(holder).values

        def isInside(parent: HeapObject): Boolean = parent match {
          case slot: HeapSlot => region(slot.owner)
          case HeapOriginal(slot) => region(slot.owner)
          case collection: HeapCollection => region(collection)
          case _ => false
        }

        val inner: Set[HeapObject] = (region -- values) ++ region.collect { case collection: HeapCollection => collection.elements }

        if (!inner.forall(node => heap.references.parentsOf(node).forall(isInside))) {
          return heap
        }

        val kept = values.minBy(value => (!value.isOriginal, value.site.expr.getPos.line, value.site.expr.getPos.col, value.site.toString))

        heap.renamed((values - kept).map(value => (value: HeapObject) -> (kept: HeapObject)).toMap)
      }

      val normalized = unshared.foldLeft(this)(normalizeCollection)

      normalized.references.references.keySet.foldLeft(normalized)(mergeTargets)
    }

    /** The heap at `scope`, without what nothing keeps alive; elements whose index goes out of scope are dropped when nothing else sees them. */
    def prune(scope: Int): HeapPointApproximation = {
      @tailrec
      def pruneFixpoint(heap: HeapPointApproximation): HeapPointApproximation = {
        val normalized = heap.normalize
        val pruned = normalized.withoutObject(normalized.deadObjects)

        if (pruned == heap) {
          return pruned
        }

        pruneFixpoint(pruned)
      }

      def pruneDanglingObject(heap: HeapPointApproximation, outOfScope: Set[Identifier]): HeapPointApproximation = {
        def isPrunable(slot: HeapElement): Boolean = {
          val roots = heap.variables ++ heap.results.values
          val targets = heap.resolveAllTargets(slot).values
          val withoutSlot = heap.withoutObject(Seq(slot))
          val visible = roots.flatMap(withoutSlot.resolveAllTargets(_).values)

          if (targets.exists(visible)) {
            return false
          }

          val elements = heap.resolveSlots(slot.owner)
          val withoutElements = heap.withoutObject(elements)
          val outside = roots.flatMap(withoutElements.resolveAllTargets(_).values)

          if (elements.forall(element => !heap.resolveAllTargets(element).values.exists(outside))) {
            return true
          }

          targets.forall(target => !target.isOriginal || HeapAccessor.fromExpression(target.site.expr)._2.contains(slot.accessor))
        }

        if (outOfScope.isEmpty) {
          return heap
        }

        val dangling = heap.objects.keySet.collect {
          case slot: HeapElement if slot.indexDependsOn(outOfScope) => slot
        }

        if (dangling.isEmpty) {
          return heap
        }

        dangling
          .find(slot => !isPrunable(slot))
          .foreach(slot => throw AliasingRewriteException.danglingIndex(slot.index))

        val withoutDangling = heap.withoutObject(dangling)

        pruneFixpoint(withoutDangling.withoutObject(withoutDangling.deadObjects))
      }

      val scoped = withScope(scope)
      val outOfScope = scoped.deadObjects.collect { case HeapVariable(identifier) => identifier }
      val pruned = pruneFixpoint(scoped.withoutObject(scoped.deadObjects))

      pruneDanglingObject(pruned, outOfScope)
    }

    /** Replaces objects as given by `substitution`, merging those that become equal. */
    def renamed(substitution: Map[HeapObject, HeapObject]): HeapPointApproximation = {
      val newObjects = objects.foldLeft(Map.empty[HeapObject, HeapScopedObject]) { case (objects, (heapObject, scoped)) =>
        val key = heapObject.substitute(substitution)

        objects.updatedWith(key) {
          case Some(existing) => Some(existing.copy(scope = existing.scope.min(scoped.scope)))
          case None => Some(HeapScopedObject(scoped.scope, key))
        }
      }

      val newReferences = references.references.foldLeft(HeapReferences.empty) { case (references, (source, reference)) =>
        val key = source.substitute(substitution)
        val substituted = reference.substitute(substitution)
        val merged = references.get(key).fold(substituted)(_.union(substituted))

        references.updated(key, merged)
      }

      val newResults = results.map { case (site, location) =>
        location.substitute(substitution) match {
          case renamedLocation: HeapLocation => site -> renamedLocation
          case other => throw new IllegalArgumentException(s"Substitution maps result location $location to non-location $other")
        }
      }

      copy(objects = newObjects, references = newReferences, results = newResults)
    }

    /** Moves `heapObject` under `registry`. */
    def withRelocate(registry: ExpressionRegistry, heapObject: HeapObject): HeapPointApproximation =
      renamed(Map(heapObject -> heapObject.relocate(registry)))

    /** Translates indices and conditions through `substitution`, from a callee's parameters to the arguments of its call. */
    def withSubstitution(substitution: Map[ValDef, Expr]): HeapPointApproximation = {
      val parameters = substitution.keySet.map(_.id)
      val indexed = objects.keySet.collect {
        case slot: HeapElement if slot.indexDependsOn(parameters) => slot
      }

      val reindexed = indexed.foldLeft(this) { (heap, slot) =>
        val reindexedSlot = slot.owner.resolveSlot(ElementAccessor(exprOps.replaceFromSymbols(substitution, slot.index)))

        heap.renamed(Map((slot: HeapObject) -> (reindexedSlot: HeapObject)))
      }

      reindexed.copy(references = reindexed.references.map(_.withSubstitution(substitution)))
    }

    /** Forgets the conditions that mention one of `identifiers`. */
    def withoutConditionOn(identifiers: Set[Identifier]): HeapPointApproximation =
      copy(references = references.map(reference => dereference(reference).withoutConditionOn(identifiers)))

    /** The values, locations and immutable values that did not exist in `before`. */
    def created(before: HeapPointApproximation): Set[HeapObject] =
      objects.keySet.collect {
        case value: HeapValue if !before.isAlive(value) => value
        case location: HeapLocation if !before.isAlive(location) => location
        case immutable: HeapImmutable if !before.isAlive(immutable) => immutable
      }

    /** Imports the slots `other` assigned and the originals it named, translating its unread originals into what this heap holds. */
    def withOverride(other: HeapPointApproximation): HeapPointApproximation = {
      val assigned = other.references.references.keySet.collect {
        case slot: HeapSlot => slot
        case original: HeapOriginal => original
      }
      val imported = copy(objects = (other.objects -- other.variables) ++ objects)

      assigned.foldLeft(imported) { (heap, source) =>
        val reference = other.references(source).flatMap {
          case HeapOriginal(original) => heap.references(original)
          case target => ExactHeapReference(target)
        }

        heap.withReference(source, reference)
      }
    }

    /** The union of both heaps: objects, references and results. */
    def merge(other: HeapPointApproximation): HeapPointApproximation = {
      if (isEmpty) {
        return other
      }

      if (other.isEmpty) {
        return this
      }

      copy(
        objects = other.objects ++ objects,
        references = withForeignReferences(other).references.union(other.withForeignReferences(this).references),
        results = results ++ other.results
      )
    }

    /** Adopts the references `other` has for objects this heap does not know. */
    private def withForeignReferences(other: HeapPointApproximation): HeapPointApproximation = {
      val adopted = other.references.references.foldLeft(references) {
        case (result, (slot: HeapSlot, reference)) if !isAlive(slot.owner) && result.get(slot).isEmpty => result.updated(slot, reference)
        case (result, (value: HeapValue, reference)) if !isAlive(value) => result.updated(value, reference)
        case (result, (original: HeapOriginal, reference)) if !isAlive(original) => result.updated(original, reference)
        case (result, _) => result
      }

      copy(references = adopted)
    }

    /** Joins the heaps of the two branches of an `if` on `condition`: registries and results are merged, references that differ become conditional on `condition`. */
    def mergeWithCondition(condition: Expr, elze: HeapPointApproximation): HeapPointApproximation = {
      if (isEmpty) {
        return elze
      }

      if (elze.isEmpty) {
        return this
      }

      val registeredHeap = exprOps
        .variablesOf(condition)
        .foldLeft(copy(objects = elze.objects ++ objects))((heap, variable) => heap.withObject(HeapVariable(variable.id)))

      registeredHeap.copy(
        references = withForeignReferences(elze).references.conditional(condition, elze.withForeignReferences(this).references),
        results = results ++ elze.results
      )
    }

    /** `reference` with every location, and every original already read, replaced by what it points to. */
    def dereference(reference: HeapReference): HeapReference = reference match {
      case ExactHeapReference(location: HeapLocation) =>
        dereference(references(location))

      case ExactHeapReference(original: HeapOriginal) if isAlive(original) =>
        dereference(references(original))

      case AmbiguousHeapReference(targets) =>
        targets.foldLeft(NoHeapReference: HeapReference)((result, target) => result.union(dereference(ExactHeapReference(target))))

      case ConditionalHeapReference(condition, thenn, elze) =>
        HeapReference.conditional(condition, dereference(thenn), dereference(elze))

      case _ =>
        reference
    }

    /** What `source` points to, then what is reached from there through `accessors`, step by step. */
    def resolveTargets(source: HeapObject, accessors: Seq[HeapAccessor] = Seq.empty): HeapTargetSet = {
      val targets = source match {
        case value: HeapValue => HeapTargetSet.of(value)
        case _ => dereference(references(source)).toTargets
      }

      accessors.foldLeft(targets) { (owners, accessor) =>
        owners.flatMap(owner => resolveTargets(HeapSlot(owner, accessor)))
      }
    }

    /** What `source` points to, and everything reachable from there through slots. */
    def resolveAllTargets(source: HeapObject): HeapTargetSet = {
      def reachFrom(value: HeapValue, visiting: Set[HeapValue]): HeapTargetSet = {
        if (visiting(value)) {
          return HeapTargetSet(Set.empty)
        }

        val children = HeapTargetSet.from(resolveSlots(value).flatMap(resolveTargets(_).targets))
        val reached = children.flatMap(child => reachFrom(child, visiting + value))

        HeapTargetSet.from(HeapTargetSet.of(value).targets ++ reached.targets)
      }

      resolveTargets(source).flatMap(reachFrom(_, Set.empty))
    }

    /** The variable paths that reach `targets`, with the targets met at each step. */
    def resolveDependencies(targets: HeapTargetSet): HeapTargetDependencySet = {
      def dependenciesOf(target: HeapTarget, visiting: Set[HeapValue]): Set[HeapTargetDependency] =
        references.holdersOf(target.value).flatMap { holder =>
          val holderTargets = resolveTargets(holder)
          val condition = holderTargets.conditionsOf(target)

          holder match {
            case _ if condition.isEmpty => Set.empty
            case HeapVariable(identifier) => Set(HeapTargetDependency(condition, identifier, Seq.empty, Seq(holderTargets)))
            case slot: HeapSlot if !visiting(slot.owner) =>
              dependenciesOf(HeapTarget(condition, slot.owner), visiting + target.value).map(_.appended(slot.accessor, holderTargets))
            case _ => Set.empty
          }
        }

      targets.targets.flatMap(dependenciesOf(_, Set.empty))
    }

    /** Whether `reference` cannot be resolved, under each of its conditions, to at most one value. */
    def isAmbiguous(reference: HeapReference): Boolean = dereference(reference) match {
      case NoHeapReference => false
      case ExactHeapReference(_: HeapValue) => false
      case ConditionalHeapReference(_, thenn, elze) => isAmbiguous(thenn) || isAmbiguous(elze)
      case _ => true
    }

    /** Whether a collection reached from `source` shares its elements with another one. */
    def isShared(source: HeapObject): Boolean =
      resolveAllTargets(source).targets.exists(target => references(target.value).toSet.size > 1)

    /** Whether what `source` reaches is a tree: no value reaches itself, and no two slots of a value reach a common object. */
    def isTree(source: HeapObject): Boolean =
      resolveAllTargets(source).targets.forall { target =>
        val reachable = resolveSlots(target.value).map(slot => resolveAllTargets(slot).restrict(target.conditions))

        val cyclic = reachable.exists(_.values.contains(target.value))
        val overlapping = reachable.combinations(2).exists { case Seq(first, second) => !first.intersect(second).isEmpty }

        !cyclic && !overlapping
      }

    /** Whether every variable path reaching what `source` points to goes through `source`. */
    def isFresh(source: HeapObject): Boolean =
      resolveDependencies(resolveAllTargets(source)).forall(_.isReachable(source))
  }

  object HeapPointApproximation {
    /** The union of `heaps`, or the empty heap at `scope` when there are none. */
    def merge(scope: Int, heaps: Seq[HeapPointApproximation]): HeapPointApproximation =
      heaps.reduceOption(_.merge(_)).getOrElse(empty(scope))

    /** The heap with nothing registered, at `scope`. */
    def empty(scope: Int): HeapPointApproximation = HeapPointApproximation(scope, Map.empty, HeapReferences.empty, Map.empty)

    /** The heap at the entry of a function: each mutable parameter points to its own original value. */
    def initial(scope: Int, params: Seq[ValDef])(using symbols: Symbols): HeapPointApproximation = {
      def declareParameter(heap: HeapPointApproximation, vd: ValDef): HeapPointApproximation = {
        if (!symbols.isMutableType(vd.tpe)) {
          return heap.withDeclareVariable(vd.id, NoHeapReference)
        }

        val (value, registered) = heap.withValue(ExpressionID(vd.toVariable), vd.tpe)

        registered.withDeclareVariable(vd.id, ExactHeapReference(value))
      }

      params.foldLeft(empty(scope))(declareParameter)
    }
  }
}
