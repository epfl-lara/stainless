/* Copyright 2009-2015 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object MergeSort {
  // Data types
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class LList
  case class LCons(head : List, tail : LList) extends LList
  case class LNil() extends LList

  def content(list : List) : Set[Int] = list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def lContent(llist : LList) : Set[Int] = llist match {
    case LNil() => Set.empty[Int]
    case LCons(x, xs) => content(x) ++ lContent(xs)
  }

  def size(list : List) : BigInt = (list match {
    case Nil() => BigInt(0)
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def isSorted(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def lIsSorted(llist : LList) : Boolean = llist match {
    case LNil() => true
    case LCons(x, xs) => isSorted(x) && lIsSorted(xs)
  }

  def abs(i : BigInt) : BigInt = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def mergeSpec(list1 : List, list2 : List, res : List) : Boolean = {
    isSorted(res) && content(res) == content(list1) ++ content(list2)
  }

  def mergeFast(list1 : List, list2 : List) : List = {
    require(isSorted(list1) && isSorted(list2))

    (list1, list2) match {
      case (_, Nil()) => list1
      case (Nil(), _) => list2
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x <= y) {
          Cons(x, mergeFast(xs, list2)) 
        } else {
          Cons(y, mergeFast(list1, ys))
        }
    }
  } ensuring(res => mergeSpec(list1, list2, res))

  def splitSpec(list : List, res : (List,List)) : Boolean = {
    val s1 = size(res._1)
    val s2 = size(res._2)
    abs(s1 - s2) <= 1 && s1 + s2 == size(list) &&
    content(res._1) ++ content(res._2) == content(list) 
  }

  def split(list : List) : (List,List) = (list match {
    case Nil() => (Nil(), Nil())
    case Cons(x, Nil()) => (Cons(x, Nil()), Nil())
    case Cons(x1, Cons(x2, xs)) =>
      val (s1,s2) = split(xs)
      (Cons(x1, s1), Cons(x2, s2))
  }) ensuring(res => splitSpec(list, res))

  def sortSpec(in : List, out : List) : Boolean = {
    content(out) == content(in) && isSorted(out)
  }

  // Not really quicksort, neither mergesort.
  def weirdSort(in : List) : List = (in match {
    case Nil() => Nil()
    case Cons(x, Nil()) => Cons(x, Nil())
    case _ =>
      val (s1,s2) = split(in)
      mergeFast(weirdSort(s1), weirdSort(s2))
  }) ensuring(res => sortSpec(in, res))

  def toLList(list : List) : LList = (list match {
    case Nil() => LNil()
    case Cons(x, xs) => LCons(Cons(x, Nil()), toLList(xs))
  }) ensuring(res => lContent(res) == content(list) && lIsSorted(res))

  def mergeMap(llist : LList) : LList = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => LNil()
      case o @ LCons(x, LNil()) => o
      case LCons(x, LCons(y, ys)) => LCons(mergeFast(x, y), mergeMap(ys))
    }
  } ensuring(res => lContent(res) == lContent(llist) && lIsSorted(res))

  def mergeReduce(llist : LList) : List = {
    require(lIsSorted(llist))

    llist match {
      case LNil() => Nil()
      case LCons(x, LNil()) => x
      case _ => mergeReduce(mergeMap(llist))
    }
  } ensuring(res => content(res) == lContent(llist) && isSorted(res))

  def mergeSort(in : List) : List = {
    mergeReduce(toLList(in))
  } ensuring(res => sortSpec(in, res))
}
