import stainless.lang._
import stainless.proof._
import stainless.annotation._
import stainless.collection._

object QuickSortFilter {

  def quickSort(ls: List[BigInt]): List[BigInt] = {
    // decreases(ls.size)
    ls match {
      case Nil() => Nil[BigInt]()
      case Cons(x, Nil()) => ls
      case Cons(x, xs) => quickSort(xs filter (_ < x)) ++ Cons(x, xs filter(_ == x)) ++ quickSort(xs filter (_ > x))
    }
  }

  def isSorted(ls: List[BigInt]): Boolean = {
    // decreases(ls)
    ls match {
      case Cons(x, xs @ Cons(y, ys)) => x <= y && isSorted(xs)
      case _ => true
    }
  }

  def append_sorted(@induct l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(isSorted(l1) && isSorted(l2) && (l1.isEmpty || l2.isEmpty || l1.last <= l2.head))
    isSorted(l1 ++ l2)
  }.holds

  def filter_equal_sorted(@induct ls: List[BigInt], x: BigInt): Boolean = {
    isSorted(ls filter (_ == x))
  }.holds

  def cons_filter_equal_sorted(ls: List[BigInt], x: BigInt): Boolean = {
    check(filter_equal_sorted(ls, x))
    isSorted(Cons(x, ls filter (_ == x)))
  }.holds

  def forall_last(@induct ls: List[BigInt], p: BigInt => Boolean): Boolean = {
    ls.forall(p) ==> (ls.isEmpty || p(ls.last))
  }.holds

  def append_preserves_forall(@induct l1: List[BigInt], l2: List[BigInt], p: BigInt => Boolean): Boolean = {
    require(l1.forall(p) && l2.forall(p))
    (l1 ++ l2).forall(p)
  }.holds

  def filter_preserves_forall(@induct ls: List[BigInt], p1: BigInt => Boolean, p2: BigInt => Boolean): Boolean = {
    require(ls.forall(p2))
    ls.filter(p1).forall(p2)
  }.holds

  def forall_lt_implies_le(@induct ls: List[BigInt], x: BigInt): Boolean = {
    require(ls.forall(_ < x))
    ls.forall(_ <= x)
  }.holds

  def forall_eq_implies_le(@induct ls: List[BigInt], x: BigInt): Boolean = {
    require(ls.forall(_ == x))
    ls.forall(_ <= x)
  }.holds

  def sort_preserves_forall(ls: List[BigInt], p: BigInt => Boolean): Boolean = {
    require(ls.forall(p))
    // decreases(ls.size)

    ls match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, xs) =>
        val less = xs filter (_ < x)
        val equal = Cons(x, xs filter (_ == x))
        val more = xs filter (_ > x)

        assert(
          filter_preserves_forall(xs, _ < x, p) &&
          filter_preserves_forall(xs, _ == x, p) &&
          filter_preserves_forall(xs, _ > x, p))

        assert(
          sort_preserves_forall(less, p) &&
          sort_preserves_forall(more, p))

        append_preserves_forall(quickSort(less), equal, p) &&
        append_preserves_forall(quickSort(less) ++ equal, quickSort(more), p)
    }

    quickSort(ls).forall(p)
  }.holds

  def sorted_lemma(ls: List[BigInt]): Boolean = {
    decreases(ls.size)

    ls match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, xs) =>
        val less = xs filter (_ < x)
        val equal = Cons(x, xs filter (_ == x))
        val more = xs filter (_ > x)

        {
          assert(sorted_lemma(less))
          assert(sort_preserves_forall(less, _ < x))
          assert(forall_last(quickSort(less), _ < x))
          assert(cons_filter_equal_sorted(xs, x))
          append_sorted(quickSort(less), equal)
        } && {
          assert(forall_lt_implies_le(less, x))
          assert(sort_preserves_forall(less, _ <= x))
          assert(forall_eq_implies_le(equal, x))
          assert(append_preserves_forall(quickSort(less), equal, _ <= x))
          assert(forall_last(quickSort(less) ++ equal, _ <= x))

          assert(sorted_lemma(more))
          assert(sort_preserves_forall(more, _ > x))
          append_sorted(quickSort(less) ++ equal, quickSort(more))
        }
    }

    isSorted(quickSort(ls))
  }.holds
}
