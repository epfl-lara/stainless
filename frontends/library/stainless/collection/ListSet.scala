package stainless.collection

import stainless.annotation._
import stainless.lang._

@library
case class ListSet[T](toList: List[T]) {
  require(ListOps.noDuplicate(toList))

  def +(elem: T): ListSet[T] = {
    if (toList.contains(elem)) {
      ListSpecs.selfContainment(toList)
      this
    } else {
      ListSpecs.prependSubset(elem, toList)
      ListSet(elem :: toList)
    }
  }.ensuring(res ⇒ res.contains(elem) && this.subsetOf(res))

  def ++(other: ListSet[T]): ListSet[T] = {
    val union = ListSetSpec.removeDuplicates(this.toList ++ other.toList)
    ListSet(union)
  }

  def -(elem: T): ListSet[T] = {
    ListSetSpec.removingFromASetResultsInASet(elem, toList)
    ListSet(toList - elem)
  }.ensuring(res ⇒ !res.contains(elem))

  def --(other: ListSet[T]): ListSet[T] = {
    ListSetSpec.listSetDiff(toList, other.toList)
    ListSpecs.restOfSetIsSubset(toList, other.toList)
    ListSet(toList -- other.toList)
  }.ensuring(res ⇒
    (res & other).isEmpty &&
    res.subsetOf(this))

  def &(other: ListSet[T]): ListSet[T] = {
    ListSetSpec.listSetIntersection(toList, other.toList)
    ListSpecs.listIntersectionLemma(toList, other.toList)
    ListSet(toList & other.toList)
  }.ensuring(res ⇒
    res.subsetOf(this) &&
    res.subsetOf(other))

  def filter(predicate: T ⇒ Boolean): ListSet[T] = {
    ListSetSpec.filteringPreservesPredicate(toList, predicate)
    ListSetSpec.filteringMakesSubset(toList, predicate)
    ListSet(toList.filter(predicate))
  }.ensuring(res ⇒ res.subsetOf(this))

  def size: BigInt = toList.size
  def isEmpty: Boolean = toList.isEmpty
  def nonEmpty: Boolean = toList.nonEmpty

  def contains(elem: T): Boolean = toList.contains(elem)
  def subsetOf(other: ListSet[T]): Boolean = toList.forall(other.toList.contains)
}

@library
object ListSet {
  def empty[T]: ListSet[T] = ListSet(List.empty[T])
}

@library
object ListSetSpec {

  @opaque
  def subsetRemovalLemma[T](original: ListSet[T], first: ListSet[T], second: ListSet[T]): Unit = {
    require(first.subsetOf(second))
    ListSpecs.removingSubsetInvertsTheRelationship(original.toList, first.toList, second.toList)
  }.ensuring(_ => (original -- second).subsetOf(original -- first))

  @opaque
  def containmentTransitivity[T](first: ListSet[T], second: ListSet[T], third: ListSet[T]): Unit = {
    require(first.subsetOf(second) && second.subsetOf(third))
    ListSpecs.transitivityLemma(first.toList, second.toList, third.toList)
  }.ensuring(_ ⇒ first.subsetOf(third))

  @opaque
  def selfContained[T](listSet: ListSet[T]): Unit = {
    ListSpecs.reflexivity(listSet.toList)
  }.ensuring(_ ⇒ listSet.subsetOf(listSet))

  @opaque
  def uniquenessTransitivity[A, B](list: List[(A, B)]): Unit = {
    require(ListOps.noDuplicate(list.map(_._1)))
    list match {
      case Nil() => ()
      case Cons(h, t) =>
        uniquenessTransitivity(t)
        pairUniquenessOnFirstElementLemma(h, t)
    }
  }.ensuring(_ => ListOps.noDuplicate(list))

  @opaque
  def pairUniquenessOnFirstElementLemma[A, B](elem: (A, B), @induct list: List[(A, B)]): Unit = {
    require(!list.map(_._1).contains(elem._1) && ListOps.noDuplicate(list))
  }.ensuring(_ => !list.contains(elem))

  @opaque
  def filteringPreservesPredicate[T](@induct list: List[T], predicate: T ⇒ Boolean): Unit = {
    require(ListOps.noDuplicate(list))
  }.ensuring(_ => ListOps.noDuplicate(list.filter(predicate)))

  @opaque
  def filteringMakesSubset[T](list: List[T], predicate: T ⇒ Boolean): Unit = {
    list match {
      case Cons(_, t) ⇒
        filteringMakesSubset(t, predicate)
        ListSpecs.tailSelfContained(list)
        ListSpecs.transitivityLemma(t.filter(predicate), t, list)
      case Nil() ⇒ ()
    }
  }.ensuring(_ => list.filter(predicate).forall(list.contains))

  @opaque
  def subsetFilteringCreatesSubsets[K, V](first: List[K], second: List[K], assignments: List[(K, V)]): Unit = {
    require(first.forall(second.contains))
    assignments match {
      case Nil() =>
      case Cons(h, t) =>
        subsetFilteringCreatesSubsets(first, second, t)
        val secondTailFiltered = t.filter(node => second.contains(node._1))
        val secondFiltered = assignments.filter(node => second.contains(node._1))
        ListSpecs.reflexivity(secondFiltered)
        assert(secondTailFiltered.forall(secondFiltered.contains))

        val firstTailFiltered = t.filter(node => first.contains(node._1))
        assert(firstTailFiltered.forall(secondTailFiltered.contains))

        if (!first.contains(h._1)) {
          ListSpecs.transitivityLemma(firstTailFiltered, secondTailFiltered, secondFiltered)
        } else {
          ListSpecs.containmentRelationship(h._1, first, second)

          ListSpecs.transitivePredicate(h._1, first.contains, second.contains)
          ListSpecs.transitivityLemma(firstTailFiltered, secondTailFiltered, secondFiltered)
        }
    }
  }.ensuring { _ =>
    val secondFiltered = assignments.filter(node => second.contains(node._1))
    val firstFiltered = assignments.filter(node => first.contains(node._1))
    firstFiltered.forall(secondFiltered.contains)
  }

  @pure
  def removingFromSet[T](@induct first: List[T], second: List[T]): List[T] = {
    require(ListOps.noDuplicate(first))
    ListSpecs.restOfSetIsSubset(first, second)
    first -- second
  }.ensuring(res => ListOps.noDuplicate(res) && (res & second).isEmpty && res.forall(first.contains))

  @opaque
  def removingDifference[T](first: List[T], second: List[T]): Unit = {
    require(first.nonEmpty && ListOps.noDuplicate(first) && first.forall(second.contains))
    first match {
      case Cons(h, Nil()) =>
        assert((second -- first.tail).contains(h))
      case Cons(h, _) =>
        assert((second -- first.tail).contains(h))
    }
  }.ensuring(_ => (second -- first.tail).contains(first.head))

  @opaque
  def listSetRemoveHeadSameAsSubtraction[T](list: List[T]): Unit = {
    require(list.nonEmpty && ListOps.noDuplicate(list))
    list match {
      case Cons(h, t) =>
        ListSpecs.removingNonContained(t, h)
    }
  }.ensuring(_ => list.tail == (list - list.head))

  @opaque
  def removingFromASetResultsInASet[T](elem: T, @induct list: List[T]): Unit = {
    require(ListOps.noDuplicate(list))
  }.ensuring(_ ⇒ ListOps.noDuplicate(list - elem))

  @opaque
  def removeDuplicates[T](list: List[T]): List[T] = {
    list match {
      case Cons(h, t) ⇒ if (t.contains(h)) removeDuplicates(t) else h :: removeDuplicates(t)
      case Nil() ⇒ Nil[T]()
    }
  }.ensuring(res ⇒ ListOps.noDuplicate(res))

  @opaque
  def listSetDiff[T](@induct first: List[T], second: List[T]): Unit = {
    require(ListOps.noDuplicate(first) && ListOps.noDuplicate(second))
  }.ensuring(_ ⇒ ListOps.noDuplicate(first -- second))

  @opaque
  def listSetIntersection[T](@induct first: List[T], second: List[T]): Unit = {
    require(ListOps.noDuplicate(first) && ListOps.noDuplicate(second))
  }.ensuring(_ ⇒ ListOps.noDuplicate(first & second))

}
