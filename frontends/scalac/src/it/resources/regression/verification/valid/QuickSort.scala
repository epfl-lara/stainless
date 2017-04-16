import stainless.proof._
import stainless.lang._
import stainless.collection._

object QuickSort {

  def isSorted(list: List[BigInt]): Boolean = {
    list match {
      case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
      case _ => true
    }
  }

  def appendSorted(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2) && (l1.isEmpty || l2.isEmpty || l1.last <= l2.head))
    l1 match {
      case Nil() => l2
      case Cons(x, xs) => Cons(x, appendSorted(xs, l2))
    }
  } ensuring { res =>
    isSorted(res) &&
    res.content == l1.content ++ l2.content
  }

  def quickSort(list: List[BigInt]): List[BigInt] = {
    decreases(list.size, BigInt(0))
    list match {
      case Nil() => Nil[BigInt]()
      case Cons(x, xs) => par(x, Nil(), Nil(), xs)
    }
  } ensuring { res =>
    isSorted(res) &&
    res.content == list.content
  }

  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(
      forall((a: BigInt) => l.contains(a) ==> a <= x) &&
      forall((a: BigInt) => r.contains(a) ==> x < a)
    )
    decreases(l.size + r.size + ls.size, ls.size + 1)

    ls match {
      case Nil() => appendSorted(quickSort(l), Cons(x, quickSort(r)))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  } ensuring { res =>
    isSorted(res) &&
    res.content == l.content ++ r.content ++ ls.content + x
  }
}
