import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

object StableSorter {

  // Inserting into a stable list adds to the content and increases the length
  def insert[T](t: T, l: List[T], key: T => BigInt): List[T] = {
    l match {
      case Nil() => t :: l
      case Cons(hd, tl) if key(t) <= key(hd) => t :: l
      case Cons(hd, tl) => hd :: insert(t, tl, key)
    }
  } ensuring { res => res.content == Set(t) ++ l.content && res.length == 1 + l.length }

  // Sorting a list preserves the content and preserves the length
  def sort[T](l: List[T], key: T => BigInt): List[T] = { l match {
    case Nil() => l
    case Cons(hd, tl) => {
      val tlSorted = sort(tl, key)
      insert(hd, tlSorted, key)
    }
  }} ensuring { res => res.content == l.content && res.length == l.length }

  // To define stability, we first annotate the input list with the initial indices...
  def annotateList[T](l: List[T], n: BigInt): List[(T, BigInt)] = {
    l match {
      case Nil() => Nil[(T, BigInt)]()
      case Cons(hd, tl) => {
        val tlAnn = annotateList(tl, n + 1)
        hint((hd, n) :: tlAnn, trivProp2(annotateList(tl, n + 1), n))
      }
    }
  } ensuring { res => l2AtLeast(res, n) }

  // ... where:
  def l2AtLeast[T](l: List[(T, BigInt)], n: BigInt): Boolean = l match {
    case Nil() => true
    case Cons((hd, hdIndex), tl) => n <= hdIndex && l2AtLeast(tl, n)
  }

  // ... and the following trivial property holds:
  @induct
  def trivProp2[T](l: List[(T, BigInt)], n: BigInt): Boolean = {
    require(l2AtLeast(l, n + 1))
    l2AtLeast(l, n)
  }.holds

  // Next, we identify an appropriate value which is increasing in a stably sorted list:
  def isStableSorted[T](l: List[(T, BigInt)], key: T => BigInt): Boolean = l match {
    case Nil() => true
    case Cons((hd, hdIndex), tl) => isStableSortedAndAtLeast(tl, key, key(hd), hdIndex)
  }

  def isStableSortedAndAtLeast[T](
    l: List[(T, BigInt)],
    key: T => BigInt,
    x: BigInt,
    minIndex: BigInt): Boolean = l match {
    case Nil() => true
    case Cons((hd, hdIndex), tl) => {
      val hdSmall = x < key(hd) || x == key(hd) && minIndex <= hdIndex
      val tlSorted = isStableSortedAndAtLeast(tl, key, key(hd), hdIndex)
      hdSmall && tlSorted
    }
  }

  // The insertion sort we initially defined is stable:
  def sortStableProp[T](l: List[T], key: T => BigInt): Boolean = {
    require(sortStablePropInt(l, 0, key))
    val lAnn = annotateList(l, 0)
    val keyAnn = (tn: (T, BigInt)) => key(tn._1)
    val lAnnSorted = sort(lAnn, keyAnn)
    isStableSorted(lAnnSorted, key)
  }.holds

  // To prove that insertion sort is stable, we first show that insertion is stable:
  @induct
  def insertStableProp[T](t: T, n: BigInt, l: List[(T, BigInt)], key: T => BigInt): Boolean = {
    require(isStableSorted(l, key) && l2AtLeast(l, n))
    val keyAnn = (tn: (T, BigInt)) => key(tn._1)
    val res = insert((t, n), l, keyAnn)
    isStableSorted(res, key) && l2AtLeast(res, n)
  }.holds

  // ... and complete the proof of stability.
  def sortStablePropInt[T](l: List[T], n: BigInt, key: T => BigInt): Boolean = {
    val lAnn = annotateList(l, n)
    val keyAnn = (tn: (T, BigInt)) => key(tn._1)
    val lAnnSorted = sort(lAnn, keyAnn)
    lAnn match {
      case Nil() => isStableSorted(lAnnSorted, key)
      case Cons((hd, hdIndex), tlAnn) => {
        val Cons(_, xs) = l
        val tlAnnSorted = sort(tlAnn, keyAnn)
        sortStablePropInt(xs, n + 1, key) &&
        n == hdIndex &&
        l2AtLeast(tlAnn, n) &&
        l2AtLeast(tlAnnSorted, n + 1) &&
        trivProp2(tlAnnSorted, n) &&
        l2AtLeast(tlAnnSorted, n) &&
        insertStableProp(hd, hdIndex, tlAnnSorted, key) &&
        isStableSorted(lAnnSorted, key) &&
        l2AtLeast(lAnnSorted, n)
      }
    }
  }.holds

  def hint[T](t: T, lemma: Boolean): T = {
    require(lemma)
    t
  }

}
