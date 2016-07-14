/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.collection._
import leon.lang._

object MergeSort2 {

  def bag[T](list: List[T]): Bag[T] = list match {
    case Nil() => Bag.empty[T]
    case Cons(x, xs) => bag(xs) + x
  }

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Cons(x1, tail @ Cons(x2, _)) => x1 <= x2 && isSorted(tail)
    case _ => true
  }

  def merge(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x <= y) Cons(x, merge(xs, l2))
        else Cons(y, merge(l1, ys))
      case _ => l1 ++ l2
    }
  } ensuring (res => isSorted(res) && bag(res) == bag(l1) ++ bag(l2))

  def split(list: List[BigInt]): (List[BigInt], List[BigInt]) = (list match {
    case Cons(x1, Cons(x2, xs)) =>
      val (s1, s2) = split(xs)
      (Cons(x1, s1), Cons(x2, s2))
    case _ => (list, Nil[BigInt]())
  }) ensuring (res => bag(res._1) ++ bag(res._2) == bag(list))

  def mergeSort(list: List[BigInt]): List[BigInt] = (list match {
    case Cons(_, Cons(_, _)) =>
      val (s1, s2) = split(list)
      merge(mergeSort(s1), mergeSort(s2))
    case _ => list
  }) ensuring (res => isSorted(res) && bag(res) == bag(list))
}
