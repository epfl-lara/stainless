/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait HeapApproximations extends CallResults { self: HeapApproximationPoints =>
  val s: Trees
  import s._

  /** Identifies one expression instance, by reference rather than by structure, within a call context. */
  final class ExpressionID(val registry: ExpressionRegistry, val expr: Expr) {
    /** Two ids are equal when they refer to the same expression instance in the same registry. */
    override def equals(other: Any): Boolean = other match {
      case that: ExpressionID => (expr.asInstanceOf[AnyRef] eq that.expr.asInstanceOf[AnyRef]) && registry == that.registry
      case _ => false
    }

    /** Consistent with `equals`: the expression is hashed by identity. */
    override def hashCode: Int = 31 * System.identityHashCode(expr) + registry.hashCode

    /** Short form for debugging: the start of the expression, its position and its call context. */
    override def toString: String = s"<${expr.toString.linesIterator.next().take(30)}@${expr.getPos.line}:${expr.getPos.col}${registry.context.fold("")(callsite => s" in $callsite")}>"
  }

  object ExpressionID {
    /** The id of `expr` in the analysed function itself, outside of any call. */
    def apply(expr: Expr): ExpressionID = ExpressionRegistry.root.resolve(expr)
  }

  /** The call context in which expressions are identified: none for the analysed function, a call for the expressions of an inlined callee. */
  final case class ExpressionRegistry private (context: Option[ExpressionID]) {
    /** The registry of the expressions seen through the call `context`. */
    def withContext(context: ExpressionID): ExpressionRegistry = ExpressionRegistry(Some(context))

    /** The id of `expr` in this registry. */
    def resolve(expr: Expr): ExpressionID = new ExpressionID(this, expr)

    /** Moves `id`, together with the chain of calls it comes from, under this registry. */
    def relocate(id: ExpressionID): ExpressionID =
      id.registry.context
        .fold(this)(context => withContext(relocate(context)))
        .resolve(id.expr)
  }

  object ExpressionRegistry {
    /** The registry of the analysed function itself. */
    val root: ExpressionRegistry = ExpressionRegistry(None)

    /** The registry of the expressions coming from the call `context`. */
    def apply(context: ExpressionID): ExpressionRegistry = root.withContext(context)
  }

  /** A node of the heap: a variable, a value, one of its slots, an element set or a location. */
  sealed abstract class HeapObject {
    /** Replaces the objects matched by `substitution`; a slot or an element set follows its owner when the owner is replaced. */
    def substitute(substitution: PartialFunction[HeapObject, HeapObject]): HeapObject = {
      def owner(value: HeapValue): HeapValue = value.substitute(substitution) match {
        case substituted: HeapValue => substituted
        case other => throw new IllegalArgumentException(s"Substitution maps owner $value of $this to non-value $other")
      }

      if (substitution.isDefinedAt(this)) {
        return substitution(this)
      }

      this match {
        case slot: HeapSlot => HeapSlot(owner(slot.owner), slot.accessor)
        case HeapOriginal(slot) => slot.substitute(substitution) match {
          case substituted: HeapSlot => HeapOriginal(substituted)
          case other => throw new IllegalArgumentException(s"Substitution maps slot $slot of $this to non-slot $other")
        }
        case elements: HeapElements => owner(elements.owner) match {
          case collection: HeapCollection => collection.elements
          case other => throw new IllegalArgumentException(s"Substitution maps owner ${elements.owner} of $this to non-collection $other")
        }
        case other => other
      }
    }

    /** Moves this object under `registry`; only locations, immutable values and values have a site to move. */
    def relocate(registry: ExpressionRegistry): HeapObject = this match {
      case HeapLocation(site) => HeapLocation(registry.relocate(site))
      case HeapImmutable(site) => HeapImmutable(registry.relocate(site))
      case other => throw new IllegalArgumentException(s"$other is not a site")
    }
  }

  /** A program variable. */
  case class HeapVariable(identifier: Identifier) extends HeapObject

  /** An object of the program, identified by the expression that produced it. */
  sealed abstract class HeapValue extends HeapObject {
    /** The expression that produced this value. */
    def site: ExpressionID

    /** The same kind of value, produced by another expression. */
    def withSite(site: ExpressionID): HeapValue = this match {
      case _: HeapInstance => HeapInstance(site)
      case _: HeapTuple => HeapTuple(site)
      case _: HeapCollection => HeapCollection(site)
    }

    /** The same value, seen as produced within the call context of `registry`. */
    override def relocate(registry: ExpressionRegistry): HeapValue =
      withSite(registry.relocate(site))

    /** Whether this value is the original content of a parameter or a slot, rather than an object created by the code. */
    def isOriginal: Boolean = site.expr match {
      case _: ClassSelector | _: TupleSelect | _: ArraySelect | _: MutableMapApply | _: Variable => true
      case _ => false
    }

    /** Whether this value has a slot reached through `accessor`. */
    def hasSlot(accessor: HeapAccessor)(using Symbols): Boolean
  }

  object HeapValue {
    /** The value produced at `site`, of the kind given by its type. */
    def apply(site: ExpressionID, tpe: Type)(using Symbols): HeapValue = tpe.getType match {
      case _: TupleType => HeapTuple(site)
      case _: ArrayType | _: MutableMapType => HeapCollection(site)
      case _ => HeapInstance(site)
    }
  }

  object HeapSlot {
    /** The slot of `owner` reached through `accessor`, whose kinds match by construction. */
    def apply(owner: HeapValue, accessor: HeapAccessor): HeapSlot = (owner, accessor) match {
      case (instance: HeapInstance, accessor: FieldAccessor) => instance.resolveSlot(accessor)
      case (tuple: HeapTuple, accessor: TupleAccessor) => tuple.resolveSlot(accessor)
      case (collection: HeapCollection, accessor: ElementAccessor) => collection.resolveSlot(accessor)
      case _ => throw new IllegalArgumentException(s"$accessor is not a component of $owner")
    }
  }

  /** A place inside a value that holds a reference: a field, a tuple component or a collection element. */
  sealed abstract class HeapSlot extends HeapObject {
    /** The value this slot belongs to. */
    def owner: HeapValue

    /** How this slot is reached from its owner. */
    def accessor: HeapAccessor

    /** The object this slot is registered under: its owner, or the element set for a collection element. */
    def parent: HeapObject
  }

  /** An instance of a class. */
  case class HeapInstance(site: ExpressionID) extends HeapValue {
    /** The slot of the field `accessor`. */
    def resolveSlot(accessor: FieldAccessor): HeapInstanceField = HeapInstanceField(this, accessor)

    /** Whether `accessor` is a field that the class of this instance, or one of its subclasses, declares. */
    def hasSlot(accessor: HeapAccessor)(using symbols: Symbols): Boolean = (accessor, site.expr.getType.getType) match {
      case (FieldAccessor(field), ct: ClassType) => (ct.tcd +: ct.tcd.descendants).exists(_.fields.exists(_.id == field))
      case _ => false
    }
  }

  /** A tuple. */
  case class HeapTuple(site: ExpressionID) extends HeapValue {
    /** The slot of the component `accessor`. */
    def resolveSlot(accessor: TupleAccessor): HeapTupleField = HeapTupleField(this, accessor)

    /** Whether `accessor` is a tuple component. */
    def hasSlot(accessor: HeapAccessor)(using Symbols): Boolean = accessor.isInstanceOf[TupleAccessor]
  }

  /** An array or a mutable map. */
  case class HeapCollection(site: ExpressionID) extends HeapValue {
    /** The elements of this collection, a node that collections sharing their elements point to. */
    def elements: HeapElements = HeapElements(this)

    /** The slot of the element at the index of `accessor`. */
    def resolveSlot(accessor: ElementAccessor): HeapElement = HeapElement(this, accessor)

    /** Whether `accessor` is an element. */
    def hasSlot(accessor: HeapAccessor)(using Symbols): Boolean = accessor.isInstanceOf[ElementAccessor]
  }

  /** A field of an instance. */
  case class HeapInstanceField(owner: HeapInstance, accessor: FieldAccessor) extends HeapSlot {
    def parent: HeapObject = owner
  }

  /** A component of a tuple. */
  case class HeapTupleField(owner: HeapTuple, accessor: TupleAccessor) extends HeapSlot {
    def parent: HeapObject = owner
  }

  /** The elements of a collection, kept apart so that several collections can share them. */
  case class HeapElements(owner: HeapCollection) extends HeapObject

  /** The element of a collection at a given index or key. */
  case class HeapElement(owner: HeapCollection, accessor: ElementAccessor) extends HeapSlot {
    def parent: HeapObject = owner.elements

    /** The index or key of this element. */
    def index: Expr = accessor.index

    /** Whether the index of this element mentions one of `identifiers`. */
    def indexDependsOn(identifiers: Set[Identifier]): Boolean = exprOps.variablesOf(index).exists(variable => identifiers(variable.id))
  }

  /** Where the result of an expression is stored. */
  case class HeapLocation(site: ExpressionID) extends HeapObject

  /** An immutable value written into a slot at `site`: not an object, but distinct for each write. */
  case class HeapImmutable(site: ExpressionID) extends HeapObject

  /** What a slot held before the code under analysis; once read, it points to the value that names it. */
  case class HeapOriginal(slot: HeapSlot) extends HeapObject

  /** An object registered in the heap, with the scope it was declared in. */
  case class HeapScopedObject(scope: Int, value: HeapObject)

  /** What an object points to: nothing, one object, one of several objects, or a choice depending on a condition. */
  sealed abstract class HeapReference {
    /** Points to the targets of both references. */
    def union(other: HeapReference): HeapReference

    /** Replaces the targets matched by `substitution`. */
    def substitute(substitution: PartialFunction[HeapObject, HeapObject]): HeapReference =
      flatMap(target => ExactHeapReference(target.substitute(substitution)))

    /** Replaces each target by the reference `f` gives for it, keeping the conditions. */
    def flatMap(f: HeapObject => HeapReference): HeapReference = this match {
      case ConditionalHeapReference(condition, thenn, elze) => HeapReference.conditional(condition, thenn.flatMap(f), elze.flatMap(f))
      case other => HeapReference.union(other.toSet.map(f))
    }

    /** Replaces the not-yet-read original by `original`. */
    def withOriginal(original: HeapObject): HeapReference = flatMap {
      case _: HeapOriginal => ExactHeapReference(original)
      case target => ExactHeapReference(target)
    }

    /** Forgets the conditions that mention one of `identifiers`, keeping the targets of both branches. */
    def withoutConditionOn(identifiers: Set[Identifier]): HeapReference = this match {
      case ConditionalHeapReference(condition, thenn, elze) if exprOps.variablesOf(condition).exists(variable => identifiers(variable.id)) =>
        thenn.withoutConditionOn(identifiers).union(elze.withoutConditionOn(identifiers))

      case ConditionalHeapReference(condition, thenn, elze) =>
        HeapReference.conditional(condition, thenn.withoutConditionOn(identifiers), elze.withoutConditionOn(identifiers))

      case other => other
    }

    /** Replaces the variables of `substitution` in every condition. */
    def withSubstitution(substitution: Map[ValDef, Expr]): HeapReference = this match {
      case ConditionalHeapReference(condition, thenn, elze) =>
        HeapReference.conditional(exprOps.replaceFromSymbols(substitution, condition), thenn.withSubstitution(substitution), elze.withSubstitution(substitution))

      case other => other
    }

    /** All the targets, whatever the conditions. */
    def toSet: Set[HeapObject]

    /** The values this reference points to, each with the conditions under which it does. */
    def toTargets: HeapTargetSet = this match {
      case ConditionalHeapReference(condition, thenn, elze) =>
        val thenTargets = thenn.toTargets.restrict(Set(HeapTargetCondition(Seq(condition -> true))))
        val elzeTargets = elze.toTargets.restrict(Set(HeapTargetCondition(Seq(condition -> false))))

        HeapTargetSet.from(thenTargets.targets ++ elzeTargets.targets)

      case other =>
        HeapTargetSet.from(other.toSet.collect { case value: HeapValue => HeapTarget(Set(HeapTargetCondition.always), value) })
    }
  }

  object HeapReference {
    /** Points to the targets of all `references`. */
    def union(references: Iterable[HeapReference]): HeapReference =
      references.foldLeft(NoHeapReference: HeapReference)(_.union(_))

    /** `thenn` when `condition` holds and `elze` otherwise, simplified: nested choices on the same condition are resolved and identical branches merged. */
    def conditional(condition: Expr, thenn: HeapReference, elze: HeapReference): HeapReference = {
      def assume(reference: HeapReference, holds: Boolean): HeapReference = reference match {
        case ConditionalHeapReference(`condition`, thenThenn, elseElze) =>
          assume(if (holds) thenThenn else elseElze, holds)

        case ConditionalHeapReference(other, otherThenn, otherElze) =>
          val assumedThenn = assume(otherThenn, holds)
          val assumedElze = assume(otherElze, holds)

          if (assumedThenn == assumedElze) assumedThenn else ConditionalHeapReference(other, assumedThenn, assumedElze)

        case other =>
          other
      }

      condition match {
        case Not(inner) => return conditional(inner, elze, thenn)
        case _ =>
      }

      val simplifiedThenn = assume(thenn, true)
      val simplifiedElze = assume(elze, false)

      if (simplifiedThenn == simplifiedElze) simplifiedThenn else ConditionalHeapReference(condition, simplifiedThenn, simplifiedElze)
    }
  }

  /** Points to nothing. */
  case object NoHeapReference extends HeapReference {
    def union(other: HeapReference): HeapReference = other

    def toSet: Set[HeapObject] = Set.empty
  }

  /** Points to exactly one object. */
  case class ExactHeapReference(reference: HeapObject) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case NoHeapReference => this
      case ExactHeapReference(r) if r == reference => this
      case ExactHeapReference(r) => AmbiguousHeapReference(Set(reference, r))
      case AmbiguousHeapReference(rs) => AmbiguousHeapReference(rs + reference)
      case conditional: ConditionalHeapReference => conditional.union(this)
    }

    def toSet: Set[HeapObject] = Set(reference)
  }

  /** Points to one of several objects, without knowing which. */
  case class AmbiguousHeapReference(references: Set[HeapObject]) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case NoHeapReference => this
      case ExactHeapReference(r) => AmbiguousHeapReference(references + r)
      case AmbiguousHeapReference(rs) => AmbiguousHeapReference(references ++ rs)
      case conditional: ConditionalHeapReference => conditional.union(this)
    }

    def toSet: Set[HeapObject] = references
  }

  /** Points to the targets of `thenn` when `condition` holds, and to those of `elze` otherwise. */
  case class ConditionalHeapReference(condition: Expr, thenn: HeapReference, elze: HeapReference) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case ConditionalHeapReference(`condition`, otherThenn, otherElze) =>
        HeapReference.conditional(condition, thenn.union(otherThenn), elze.union(otherElze))

      case _ =>
        HeapReference.conditional(condition, thenn.union(other), elze.union(other))
    }

    def toSet: Set[HeapObject] = thenn.toSet ++ elze.toSet
  }

  /** The references of all objects, with the reverse index from each target to the objects pointing to it. */
  case class HeapReferences private (
    references: Map[HeapObject, HeapReference],
    parents: Map[HeapObject, Set[HeapObject]]
  ) {
    /** What `source` points to; a slot that was never assigned points to its original. */
    def apply(source: HeapObject): HeapReference = references.getOrElse(source, default(source))

    /** What `source` was explicitly assigned, if anything. */
    def get(source: HeapObject): Option[HeapReference] = references.get(source)

    /** The objects pointing directly to `target`. */
    def parentsOf(target: HeapObject): Set[HeapObject] = parents.getOrElse(target, Set.empty)

    /** The variables and slots that point to `target`, through any locations or read originals in between; a read original is also held by its own slot. */
    def holdersOf(target: HeapObject): Set[HeapObject] = {
      def holdersFrom(node: HeapObject, visited: Set[HeapObject]): Set[HeapObject] =
        parentsOf(node).flatMap {
          case location: HeapLocation if visited(location) => Set.empty
          case location: HeapLocation => holdersFrom(location, visited + location)
          case original: HeapOriginal if visited(original) => Set.empty
          case original: HeapOriginal => holdersFrom(original, visited + original) + original.slot
          case holder => Set(holder)
        }

      holdersFrom(target, Set.empty)
    }

    /** Makes `source` point to `reference`, keeping the reverse index in sync. */
    def updated(source: HeapObject, reference: HeapReference): HeapReferences = {
      val withoutPrevious = apply(source)
        .toSet
        .foldLeft(parents) { (parents, target) =>
          parents.updatedWith(target)(_.map(_ - source).filter(_.nonEmpty))
        }

      val withCurrent = reference
        .toSet
        .foldLeft(withoutPrevious) { (parents, target) =>
          parents.updatedWith(target)(sources => Some(sources.getOrElse(Set.empty) + source))
        }

      val newReferences =
        if (reference == default(source)) references - source
        else references + (source -> reference)

      HeapReferences(newReferences, withCurrent)
    }

    /** What `source` points to when it was never assigned: its original for a slot, nothing otherwise. */
    private def default(source: HeapObject): HeapReference = source match {
      case slot: HeapSlot => ExactHeapReference(HeapOriginal(slot))
      case _ => NoHeapReference
    }

    /** The objects `source` ends up at, following references until a value or an object pointing to nothing. */
    def resolve(source: HeapObject): Set[HeapObject] = {
      def resolveFrom(source: HeapObject, visited: Set[HeapObject]): Set[HeapObject] = {
        if (visited(source)) {
          return Set.empty
        }

        val targets = apply(source).toSet

        if (source.isInstanceOf[HeapValue] || targets.isEmpty) {
          return Set(source)
        }

        targets.flatMap(resolveFrom(_, visited + source))
      }

      resolveFrom(source, Set.empty)
    }

    /** Points each object to the targets it has in either map. */
    def union(other: HeapReferences): HeapReferences =
      (references.keySet ++ other.references.keySet).foldLeft(this) { (result, source) =>
        result.updated(source, apply(source).union(other(source)))
      }

    /** Points each object to what it has in this map when `condition` holds, and in `elze` otherwise. */
    def conditional(condition: Expr, elze: HeapReferences): HeapReferences =
      (references.keySet ++ elze.references.keySet).foldLeft(this) { (result, source) =>
        result.updated(source, HeapReference.conditional(condition, apply(source), elze(source)))
      }

    /** Rewrites every reference with `f`. */
    def map(f: HeapReference => HeapReference): HeapReferences =
      references.foldLeft(HeapReferences.empty) { case (result, (source, reference)) =>
        result.updated(source, f(reference))
      }

    /** Drops the references of the objects in `pruned`. */
    def prune(pruned: Set[HeapObject]): HeapReferences =
      references.foldLeft(HeapReferences.empty) {
        case (result, (source, _)) if pruned(source) => result
        case (result, (source, reference)) => result.updated(source, reference)
      }
  }

  object HeapReferences {
    /** No references at all. */
    val empty: HeapReferences = HeapReferences(Map.empty, Map.empty)
  }

  /** A conjunction of choices, each a condition with the value it must have. */
  case class HeapTargetCondition(choices: Seq[(Expr, Boolean)]) {
    /** Whether both conjunctions require some condition to have opposite values, so that they never hold together. */
    def isDisjoint(other: HeapTargetCondition): Boolean =
      choices.exists { case (condition, holds) => other.choices.contains(condition -> !holds) }

    /** Both conjunctions at once. */
    def and(other: HeapTargetCondition): HeapTargetCondition =
      HeapTargetCondition((choices ++ other.choices).distinct)
  }

  object HeapTargetCondition {
    /** The empty conjunction, which always holds. */
    val always: HeapTargetCondition = HeapTargetCondition(Seq.empty)

    /** The disjunction of `conditions` as an expression, positioned at `tree`. */
    def toExpression(conditions: Set[HeapTargetCondition], tree: Expr): Expr = {
      if (conditions.exists(_.choices.isEmpty)) {
        return BooleanLiteral(true).copiedFrom(tree)
      }

      val disjuncts = conditions.toSeq.map { condition =>
        andJoin(condition.choices.map { case (choice, holds) => if (holds) choice else Not(choice).copiedFrom(tree) })
      }

      orJoin(disjuncts)
    }

    /** The conjunctions of one condition from `first` and one from `second` that can hold together. */
    def and(first: Set[HeapTargetCondition], second: Set[HeapTargetCondition]): Set[HeapTargetCondition] =
      for {
        firstCondition <- first
        secondCondition <- second
        if !firstCondition.isDisjoint(secondCondition)
      } yield firstCondition.and(secondCondition)
  }

  /** A value pointed to, with the conditions under which it is. */
  case class HeapTarget(conditions: Set[HeapTargetCondition], value: HeapValue) {
    /** The same value, under other conditions. */
    def withConditions(conditions: Set[HeapTargetCondition]): HeapTarget = copy(conditions = conditions)
  }

  /** The values something may point to, each with its conditions. */
  case class HeapTargetSet(targets: Set[HeapTarget]) {
    /** The values, whatever the conditions. */
    def values: Set[HeapValue] = targets.map(_.value)

    /** Whether no value can be pointed to. */
    def isEmpty: Boolean = targets.isEmpty

    /** The conditions under which `value` is pointed to. */
    def conditionsOf(value: HeapValue): Set[HeapTargetCondition] =
      targets
        .find(_.value == value)
        .fold(Set.empty[HeapTargetCondition])(_.conditions)

    /** The conditions under which this set points to `target`, compatible with those of `target`. */
    def conditionsOf(target: HeapTarget): Set[HeapTargetCondition] =
      restrict(target.conditions).conditionsOf(target.value)

    /** Whether no two values can be pointed to at the same time. */
    def isDisjoint: Boolean =
      targets.forall(first => targets.forall(second => first == second || first.conditions.forall(condition => second.conditions.forall(condition.isDisjoint))))

    /** The values found in both sets, under the conditions where both point to them. */
    def intersect(other: HeapTargetSet): HeapTargetSet = {
      val intersected = targets
        .map(target => target.withConditions(HeapTargetCondition.and(target.conditions, other.conditionsOf(target.value))))
        .filter(_.conditions.nonEmpty)

      HeapTargetSet(intersected)
    }

    /** The targets satisfying `predicate`. */
    def filter(predicate: HeapTarget => Boolean): HeapTargetSet =
      HeapTargetSet(targets.filter(predicate))

    /** For each value, the targets `f` gives for it, under the conditions of both. */
    def flatMap(f: HeapValue => HeapTargetSet): HeapTargetSet =
      HeapTargetSet.from(targets.flatMap(target => f(target.value).restrict(target.conditions).targets))

    /** The targets that can still be pointed to once `conditions` are also required. */
    def restrict(conditions: Set[HeapTargetCondition]): HeapTargetSet = {
      val restricted = targets
        .map(target => target.withConditions(HeapTargetCondition.and(conditions, target.conditions)))
        .filter(_.conditions.nonEmpty)

      HeapTargetSet(restricted)
    }
  }

  object HeapTargetSet {
    /** `value`, pointed to unconditionally. */
    def of(value: HeapValue): HeapTargetSet = HeapTargetSet(Set(HeapTarget(Set(HeapTargetCondition.always), value)))

    /** Groups `targets` by value, merging their conditions. */
    def from(targets: Iterable[HeapTarget]): HeapTargetSet = {
      val grouped = targets
        .groupBy(_.value)
        .map { case (value, group) => HeapTarget(group.flatMap(_.conditions).toSet, value) }
        .toSet

      HeapTargetSet(grouped)
    }
  }

  /** One step from a value to one of its slots. */
  sealed abstract class HeapAccessor

  /** A class field. */
  case class FieldAccessor(identifier: Identifier) extends HeapAccessor

  /** A tuple component, counted from 1. */
  case class TupleAccessor(index: Int) extends HeapAccessor

  /** A collection element, at an index or key. */
  case class ElementAccessor(index: Expr) extends HeapAccessor

  object HeapAccessor {
    /** Splits a selection such as `a.f(i)._1` into its base and the steps leading from it, skipping casts and annotations. */
    def fromExpression(e: Expr): (Expr, Seq[HeapAccessor]) = e match {
      case ClassSelector(owner, field) => appended(owner, FieldAccessor(field))
      case TupleSelect(owner, index) => appended(owner, TupleAccessor(index))
      case ArraySelect(owner, index) => appended(owner, ElementAccessor(index))
      case MutableMapApply(owner, key) => appended(owner, ElementAccessor(key))
      case AsInstanceOf(owner, _) => fromExpression(owner)
      case Annotated(owner, _) => fromExpression(owner)
      case _ => (e, Seq.empty)
    }

    /** Rebuilds the selection of `accessors` from `base`. */
    def toExpression(base: Expr, accessors: Seq[HeapAccessor])(using Symbols): Expr = accessors.foldLeft(base) {
      case (owner, FieldAccessor(field)) => select(owner, field)
      case (owner, TupleAccessor(index)) => TupleSelect(owner, index).copiedFrom(owner)
      case (owner, ElementAccessor(index)) => owner.getType.getType match {
        case _: ArrayType => ArraySelect(owner, index).copiedFrom(owner)
        case _: MutableMapType => MutableMapApply(owner, index).copiedFrom(owner)
        case _ => throw AliasingRewriteException.unrebuildableValue(owner)
      }
    }

    /** Selects `field` on `receiver`, casting it to the class that declares the field when needed. */
    def select(receiver: Expr, field: Identifier)(using Symbols): Expr =
      ClassSelector(narrow(receiver, field)._1, field).copiedFrom(receiver)

    /** Casts `receiver` to the class that declares `field`, and returns that class type. */
    def narrow(receiver: Expr, field: Identifier)(using symbols: Symbols): (Expr, ClassType) = receiver.getType.getType match {
      case receiverType: ClassType =>
        val fieldClass = symbols.classForField(receiverType, field).getOrElse(throw AliasingRewriteException.unknownFieldOwner(receiver))
        val fieldClassType = fieldClass.toType

        (castTo(receiver, fieldClassType), fieldClassType)

      case _ =>
        throw AliasingRewriteException.unrebuildableValue(receiver)
    }

    /** Casts `value` to `tpe`, unless it already has that type. */
    def castTo(value: Expr, tpe: Type)(using symbols: Symbols): Expr =
      if (symbols.isSubtypeOf(value.getType, tpe)) value
      else Annotated(AsInstanceOf(value, tpe).copiedFrom(value), Seq(DropVCs)).copiedFrom(value)

    /** `base` with the part reached through `accessors` replaced by `value`, rebuilding every value along the way. */
    def updated(base: Expr, accessors: Seq[HeapAccessor], value: Expr)(using Symbols): Expr = {
      def updatedClass(receiver: Expr, field: Identifier, value: Expr): Expr = {
        val (narrowedReceiver, fieldClassType) = narrow(receiver, field)
        val rebuiltReceiver = ClassConstructor(fieldClassType, fieldClassType.tcd.fields.map { vd =>
          if (vd.id == field) castTo(value, vd.tpe)
          else ClassSelector(narrowedReceiver, vd.id).copiedFrom(receiver)
        }).copiedFrom(value)

        castTo(rebuiltReceiver, receiver.getType)
      }

      def updatedTuple(receiver: Expr, index: Int, value: Expr): Expr = receiver.getType.getType match {
        case TupleType(bases) =>
          Tuple(bases.indices.map { position =>
            if (position + 1 == index) castTo(value, bases(position))
            else TupleSelect(receiver, position + 1).copiedFrom(receiver)
          }).copiedFrom(value)

        case _ =>
          throw AliasingRewriteException.unrebuildableValue(receiver)
      }

      accessors match {
        case Seq() => castTo(value, base.getType)
        case FieldAccessor(field) +: rest => updatedClass(base, field, updated(select(base, field), rest, value))
        case TupleAccessor(index) +: rest => updatedTuple(base, index, updated(TupleSelect(base, index).copiedFrom(base), rest, value))
        case ElementAccessor(index) +: rest => base.getType.getType match {
          case _: ArrayType => ArrayUpdated(base, index, updated(ArraySelect(base, index).copiedFrom(base), rest, value)).copiedFrom(base)
          case _: MutableMapType => MutableMapUpdated(base, index, updated(MutableMapApply(base, index).copiedFrom(base), rest, value)).copiedFrom(base)
          case _ => throw AliasingRewriteException.unrebuildableValue(base)
        }
      }
    }

    /** The base and steps of `owner`, followed by `accessor`. */
    private def appended(owner: Expr, accessor: HeapAccessor): (Expr, Seq[HeapAccessor]) = {
      val (base, accessors) = fromExpression(owner)

      (base, accessors :+ accessor)
    }
  }

  /** A way to reach some targets from a variable: under `condition`, through `accessors`, with the targets found at each step. */
  case class HeapTargetDependency(condition: Set[HeapTargetCondition], variable: Identifier, accessors: Seq[HeapAccessor], targets: Seq[HeapTargetSet]) {
    /** Whether every step of the path points to values that cannot be confused. */
    def isDisjoint: Boolean = targets.forall(_.isDisjoint)

    /** The same path, continued through `accessor` to `step`. */
    def appended(accessor: HeapAccessor, step: HeapTargetSet): HeapTargetDependency =
      copy(accessors = accessors :+ accessor, targets = targets :+ step)

    /** Whether `other` starts with this path: the same variable, then the accessors of this path. */
    def isPrefixOf(other: HeapTargetDependency): Boolean =
      variable == other.variable && other.accessors.startsWith(accessors)

    /** The slots this path goes through. */
    def slots: Set[HeapSlot] =
      targets
        .zip(accessors)
        .flatMap { case (owners, accessor) => owners.values.map(HeapSlot(_, accessor)) }
        .toSet

    /** The values this path reaches. */
    def values: Set[HeapValue] = targets.flatMap(_.values).toSet

    /** Whether `heapObject` is on this path: a value it reaches, or a variable or slot it goes through. */
    def isReachable(heapObject: HeapObject): Boolean = heapObject match {
      case value: HeapValue => values(value)
      case HeapVariable(identifier) => variable == identifier
      case slot: HeapSlot => slots(slot)
      case _ => false
    }
  }

  /** All the ways to reach some targets. */
  type HeapTargetDependencySet = Set[HeapTargetDependency]
}
