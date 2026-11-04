/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative


trait HeapApproximations extends CallResults { self: HeapApproximationPoints =>
  val s: Trees
  import s._

  final class ExpressionID(val context: Option[ExpressionID], val expr: Expr) {
    def within(callsite: ExpressionID): ExpressionID =
      ExpressionID(Some(context.fold(callsite)(_.within(callsite))), expr)

    override def equals(other: Any): Boolean = other match {
      case that: ExpressionID => (expr.asInstanceOf[AnyRef] eq that.expr.asInstanceOf[AnyRef]) && context == that.context
      case _ => false
    }

    override def hashCode: Int = 31 * System.identityHashCode(expr) + context.hashCode

    override def toString: String = s"<${expr.toString.linesIterator.next().take(30)}@${expr.getPos.line}:${expr.getPos.col}${context.fold("")(callsite => s" in $callsite")}>"
  }

  object ExpressionID {
    val RootContext: Option[ExpressionID] = None

    def apply(context: Option[ExpressionID], expr: Expr): ExpressionID = new ExpressionID(context, expr)

    def apply(expr: Expr): ExpressionID = new ExpressionID(RootContext, expr)
  }

  sealed abstract class HeapObject {
    def substitute(substitution: HeapSubstitution): HeapObject = {
      if (substitution.contains(this)) {
        return substitution(this)
      }

      this match {
        case HeapInstanceField(owner, identifier) => HeapInstanceField(owner.substitute(substitution), identifier)
        case HeapTupleField(owner, index) => HeapTupleField(owner.substitute(substitution), index)
        case HeapElements(owner) => owner.substitute(substitution) match {
          case instance: HeapInstance => HeapElements(instance)
          case other => throw new IllegalArgumentException(s"Substitution maps elements owner $owner to non-instance $other")
        }
        
        case HeapElement(elements, index) => elements.substitute(substitution) match {
          case substituted: HeapElements => HeapElement(substituted, index)
          case other => throw new IllegalArgumentException(s"Substitution maps elements $elements to non-elements $other")
        }

        case other => other
      }
    }

    def within(callsite: ExpressionID): HeapObject = this match {
      case HeapInstance(site) => HeapInstance(site.within(callsite))
      case HeapLocation(site) => HeapLocation(site.within(callsite))
      case other => throw new IllegalArgumentException(s"$other is not a site")
    }
  }

  case class HeapVariable(identifier: Identifier) extends HeapObject
  case class HeapInstance(site: ExpressionID) extends HeapObject
  case class HeapInstanceField(owner: HeapObject, identifier: Identifier) extends HeapObject
  case class HeapTupleField(owner: HeapObject, index: Int) extends HeapObject
  case class HeapElements(owner: HeapInstance) extends HeapObject
  case class HeapElement(elements: HeapElements, index: Expr) extends HeapObject
  sealed abstract class HeapAddress extends HeapObject

  case class HeapLocation(site: ExpressionID) extends HeapAddress

  case class HeapRecursiveAddress(site: ExpressionID)(initialize: HeapRecursiveAddress => (HeapReference, HeapPointApproximation)) extends HeapAddress {
    lazy val representation: (HeapReference, HeapPointApproximation) = initialize(this)

    private val rescoped = scala.collection.mutable.Map.empty[ExpressionID, HeapRecursiveAddress]

    override def within(callsite: ExpressionID): HeapRecursiveAddress =
      rescoped.getOrElseUpdate(callsite, HeapRecursiveAddress(site.within(callsite))(initialize))
  }

  case class HeapScopedObject(scope: Int, value: HeapObject, children: Set[HeapObject] = Set.empty)

  final class HeapSubstitution private (val mapping: Map[HeapObject, HeapObject]) {
    def contains(heapObject: HeapObject): Boolean = mapping.contains(heapObject)

    def apply(heapObject: HeapObject): HeapObject = mapping(heapObject)
  }

  object HeapSubstitution {
    def apply(mapping: Map[HeapObject, HeapObject]): HeapSubstitution = {
      if (mapping.values.toSet.size != mapping.size) {
        throw new IllegalArgumentException(s"Substitution $mapping maps distinct objects to the same object")
      }

      new HeapSubstitution(mapping)
    }

    def union(substitutions: Seq[HeapSubstitution]): HeapSubstitution =
      HeapSubstitution(substitutions.foldLeft(Map.empty[HeapObject, HeapObject]) { (mapping, substitution) =>
        substitution.mapping.foldLeft(mapping) { case (mapping, (heapObject, image)) =>
          if (mapping.get(heapObject).exists(_ != image)) {
            throw new IllegalArgumentException(s"$heapObject is mapped to both ${mapping(heapObject)} and $image")
          }

          mapping + (heapObject -> image)
        }
      })
  }

  case class HeapObjectStructure(instance: HeapObject, children: Map[HeapAccessor, HeapObjectStructure]) {
    def substitution(other: HeapObjectStructure): HeapSubstitution =
      HeapSubstitution.union(HeapSubstitution(Map(instance -> other.instance)) +: children.toSeq.map { case (accessor, child) => child.substitution(other.children(accessor)) })
  }

  case class HeapObjectRepresentation(instance: HeapObject, children: Map[HeapAccessor, Set[HeapObjectRepresentation]]) {
    def alternatives: Seq[HeapObjectStructure] =
      children.foldLeft(Seq(HeapObjectStructure(instance, Map.empty))) { case (structures, (accessor, representations)) =>
        for {
          structure <- structures
          representation <- representations.toSeq
          child <- representation.alternatives
        } yield structure.copy(children = structure.children + (accessor -> child))
      }
  }

  sealed abstract class HeapReference {
    def union(other: HeapReference): HeapReference

    def substitute(substitution: HeapSubstitution): HeapReference = this match {
      case NoHeapReference => this
      case ExactHeapReference(reference) => ExactHeapReference(reference.substitute(substitution))
      case AmbiguousHeapReference(references) => references.foldLeft(NoHeapReference: HeapReference)((result, target) => result.union(ExactHeapReference(target.substitute(substitution))))
      case ConditionalHeapReference(condition, thenn, elze) => HeapReference.conditional(condition, thenn.substitute(substitution), elze.substitute(substitution))
    }

    def prune(identifiers: Set[Identifier]): HeapReference = this match {
      case ConditionalHeapReference(condition, thenn, elze) if exprOps.variablesOf(condition).exists(variable => identifiers(variable.id)) => thenn.prune(identifiers).union(elze.prune(identifiers))
      case ConditionalHeapReference(condition, thenn, elze) => HeapReference.conditional(condition, thenn.prune(identifiers), elze.prune(identifiers))
      case other => other
    }

    def mapLeaves(missing: HeapReference)(leaf: HeapObject => HeapReference): HeapReference = this match {
      case ConditionalHeapReference(condition, thenn, elze) => HeapReference.conditional(condition, thenn.mapLeaves(missing)(leaf), elze.mapLeaves(missing)(leaf))
      case NoHeapReference => missing
      case other => other.toSet().foldLeft(NoHeapReference: HeapReference)((result, target) => result.union(leaf(target)))
    }

    def toSet(): Set[HeapObject]
  }

  object HeapReference {
    def conditional(condition: Expr, thenn: HeapReference, elze: HeapReference): HeapReference = {
      condition match {
        case Not(inner) => return conditional(inner, elze, thenn)
        case _ =>
      }

      def assume(reference: HeapReference, holds: Boolean): HeapReference = reference match {
        case ConditionalHeapReference(`condition`, thenThenn, elseElze) => assume(if (holds) thenThenn else elseElze, holds)
        case ConditionalHeapReference(other, otherThenn, otherElze) =>
          val assumedThenn = assume(otherThenn, holds)
          val assumedElze = assume(otherElze, holds)
          if (assumedThenn == assumedElze) assumedThenn else ConditionalHeapReference(other, assumedThenn, assumedElze)
          
        case other => other
      }

      val simplifiedThenn = assume(thenn, true)
      val simplifiedElze = assume(elze, false)

      if (simplifiedThenn == simplifiedElze) simplifiedThenn else ConditionalHeapReference(condition, simplifiedThenn, simplifiedElze)
    }
  }

  case object NoHeapReference extends HeapReference {
    def union(other: HeapReference): HeapReference = other

    def toSet(): Set[HeapObject] = Set.empty
  }

  case class ExactHeapReference(reference: HeapObject) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case NoHeapReference => this
      case ExactHeapReference(r) if r == reference => this
      case ExactHeapReference(r) => AmbiguousHeapReference(Set(reference, r))
      case AmbiguousHeapReference(rs) => AmbiguousHeapReference(rs + reference)
      case conditional: ConditionalHeapReference => conditional.union(this)
    }

    def toSet(): Set[HeapObject] = Set(reference)
  }

  case class AmbiguousHeapReference(references: Set[HeapObject]) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case NoHeapReference => this
      case ExactHeapReference(r) => AmbiguousHeapReference(references + r)
      case AmbiguousHeapReference(rs) => AmbiguousHeapReference(references ++ rs)
      case conditional: ConditionalHeapReference => conditional.union(this)
    }

    def toSet(): Set[HeapObject] = references
  }

  case class ConditionalHeapReference(condition: Expr, thenn: HeapReference, elze: HeapReference) extends HeapReference {
    def union(other: HeapReference): HeapReference = other match {
      case ConditionalHeapReference(`condition`, otherThenn, otherElze) =>
        HeapReference.conditional(condition, thenn.union(otherThenn), elze.union(otherElze))

      case _ =>
        HeapReference.conditional(condition, thenn.union(other), elze.union(other))
    }

    def toSet(): Set[HeapObject] = thenn.toSet() ++ elze.toSet()
  }

  case class HeapReferences private (
    references: Map[HeapObject, HeapReference],
    parents: Map[HeapObject, Set[HeapObject]]
  ) {
    def apply(source: HeapObject): HeapReference = references.getOrElse(source, NoHeapReference)

    def parentsOf(target: HeapObject): Set[HeapObject] = parents.getOrElse(target, Set.empty)

    def updated(source: HeapObject, reference: HeapReference): HeapReferences = {
      val withoutPrevious = apply(source).toSet().foldLeft(parents) { (parents, target) =>
        parents.updatedWith(target)(_.map(_ - source).filter(_.nonEmpty))
      }

      val withCurrent = reference.toSet().foldLeft(withoutPrevious) { (parents, target) =>
        parents.updatedWith(target)(sources => Some(sources.getOrElse(Set.empty) + source))
      }
      
      val newReferences = reference match {
        case NoHeapReference => references - source
        case _ => references + (source -> reference)
      }

      HeapReferences(newReferences, withCurrent)
    }

    /** The objects `source` resolves to, following references until only objects pointing to nothing remain. */
    def resolve(source: HeapObject): Set[HeapObject] = {
      def resolveFrom(source: HeapObject, visited: Set[HeapObject]): Set[HeapObject] = {
        if (visited(source)) {
          return Set.empty
        }

        val targets = apply(source).toSet()
        if (targets.isEmpty) {
          return Set(source)
        }

        targets.flatMap(resolveFrom(_, visited + source))
      }

      resolveFrom(source, Set.empty)
    }

    def combine(other: HeapReferences)(f: (HeapReference, HeapReference) => HeapReference): HeapReferences =
      (references.keySet ++ other.references.keySet).foldLeft(this) { (result, source) =>
        val current = apply(source)
        val combined = f(current, other(source))

        if (combined == current) result else result.updated(source, combined)
      }

    def prune(pruned: Set[HeapObject]): HeapReferences = {
      val identifiers = pruned.collect { case HeapVariable(identifier) => identifier }

      references.foldLeft(HeapReferences.empty) {
        case (result, (source, _)) if pruned(source) => result
        case (result, (source, reference)) => result.updated(source, reference.prune(identifiers))
      }
    }
  }

  object HeapReferences {
    val empty: HeapReferences = HeapReferences(Map.empty, Map.empty)
  }

  case class HeapTargetCondition(choices: Seq[(Expr, Boolean)]) {
    def isDisjoint(other: HeapTargetCondition): Boolean =
      choices.exists { case (condition, holds) => other.choices.contains(condition -> !holds) }

    def and(other: HeapTargetCondition): HeapTargetCondition =
      HeapTargetCondition((choices ++ other.choices).distinct)
  }

  object HeapTargetCondition {
    def and(first: Set[HeapTargetCondition], second: Set[HeapTargetCondition]): Set[HeapTargetCondition] =
      for {
        firstCondition <- first
        secondCondition <- second
        if !firstCondition.isDisjoint(secondCondition)
      } yield firstCondition.and(secondCondition)
  }

  case class HeapTarget(conditions: Set[HeapTargetCondition], instance: HeapInstance) {
    def withConditions(conditions: Set[HeapTargetCondition]): HeapTarget = copy(conditions = conditions)
  }

  case class HeapTargetSet(targets: Set[HeapTarget]) {
    def conditionsOf(instance: HeapInstance): Set[HeapTargetCondition] =
      targets.find(_.instance == instance).fold(Set.empty[HeapTargetCondition])(_.conditions)

    def isDisjoint: Boolean =
      targets.forall(first => targets.forall(second => first == second || first.conditions.forall(condition => second.conditions.forall(condition.isDisjoint))))

    def intersect(other: HeapTargetSet): HeapTargetSet =
      HeapTargetSet(targets.map(target => target.withConditions(HeapTargetCondition.and(target.conditions, other.conditionsOf(target.instance)))).filter(_.conditions.nonEmpty))

    def filter(predicate: HeapTarget => Boolean): HeapTargetSet =
      HeapTargetSet(targets.filter(predicate))
  }

  object HeapTargetSet {
    def from(targets: Iterable[HeapTarget]): HeapTargetSet =
      HeapTargetSet(targets.groupBy(_.instance).map { case (instance, group) =>
        HeapTarget(group.flatMap(_.conditions).toSet, instance)
      }.toSet)
  }

  sealed abstract class HeapAccessor
  case class FieldAccessor(identifier: Identifier) extends HeapAccessor
  case class TupleAccessor(index: Int) extends HeapAccessor
  case class ElementAccessor(index: Expr) extends HeapAccessor

  object HeapAccessor {
    def fromExpression(e: Expr): (Expr, Seq[HeapAccessor]) = e match {
      case ClassSelector(owner, field) => appended(owner, FieldAccessor(field))
      case TupleSelect(owner, index) => appended(owner, TupleAccessor(index))
      case ArraySelect(owner, index) => appended(owner, ElementAccessor(index))
      case MutableMapApply(owner, key) => appended(owner, ElementAccessor(key))
      case AsInstanceOf(owner, _) => fromExpression(owner)
      case Annotated(owner, _) => fromExpression(owner)
      case _ => (e, Seq.empty)
    }

    private def appended(owner: Expr, accessor: HeapAccessor): (Expr, Seq[HeapAccessor]) = {
      val (base, accessors) = fromExpression(owner)
      (base, accessors :+ accessor)
    }
  }

  case class HeapTargetDependency(condition: Set[HeapTargetCondition], variable: Identifier, accessors: Seq[HeapAccessor], targets: Seq[HeapTargetSet]) {
    def isDisjoint: Boolean = targets.forall(_.isDisjoint)
  }

  type HeapTargetDependencySet = Set[HeapTargetDependency]
}
