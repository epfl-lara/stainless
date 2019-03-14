import stainless.annotation._
import stainless.lang._

object QuickSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = {
    decreases(l)
    l match {
      case Nil() => BigInt(0)
      case Cons(x, xs) => 1 + size(xs)
    }
  } ensuring((res: BigInt) => res >= 0)

  def contents(l: List): Set[Int] = {
    decreases(l)
    l match {
      case Nil() => Set.empty
      case Cons(x,xs) => contents(xs) ++ Set(x)
    }
  }

  def is_sorted(l: List): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x,Nil()) => true
      case Cons(x,Cons(y,xs)) => x <= y && is_sorted(Cons(y,xs))
    }
  }

  def rev_append(aList: List, bList: List): List = {
    decreases(aList)
    aList match {
      case Nil() => bList
      case Cons(x,xs) => rev_append(xs, Cons(x, bList))
    }
  }

  def reverse(list: List): List = rev_append(list,Nil())

  def append(aList: List, bList: List): List = {
    aList match {
      case Nil() => bList
      case _ => rev_append(reverse(aList),bList)
    }
  }

  def greater(n:Int, list:List) : List = {
    decreases(list)
    list match {
      case Nil() => Nil()
      case Cons(x,xs) => if (n < x) Cons(x, greater(n,xs)) else greater(n,xs)
    }
  } ensuring(res => size(res) <= size(list))

  def smaller(n: Int, list: List) : List = {
    decreases(list)
    list match {
      case Nil() => Nil()
      case Cons(x,xs) => if (n > x) Cons(x, smaller(n,xs)) else smaller(n,xs)
    }
  } ensuring(res => size(res) <= size(list))

  def equals(n: Int, list: List) : List = {
    decreases(list)
    list match {
      case Nil() => Nil()
      case Cons(x,xs) => if (n==x) Cons(x,equals(n,xs)) else equals(n,xs)
    }
  }

  def quickSort(list: List): List = {
    decreases(size(list))
    list match {
      case Nil() => Nil()
      case Cons(x, Nil()) => list
      case Cons(x, xs) =>
        append(
          append(
            quickSort(smaller(x,xs)),
            Cons(x,equals(x,xs))
          ),
          quickSort(greater(x,xs))
        )
    }
  }
}
