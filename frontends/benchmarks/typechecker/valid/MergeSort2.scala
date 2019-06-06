/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.annotation._
import stainless.collection._
import stainless.lang._

object MergeSort2 {

  def bag[T](list: List[T]): Bag[T] = {
    decreases(list)
    list match {
      case Nil() => Bag.empty[T]
      case Cons(x, xs) => bag(xs) + x
    }
  }

  def isSorted(list: List[BigInt]): Boolean = {
    decreases(list)
    list match {
      case Cons(x1, tail @ Cons(x2, _)) => x1 <= x2 && isSorted(tail)
      case _ => true
    }
  }

  def merge(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2))
    decreases(l1,l2)

    (l1, l2) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x <= y) Cons(x, merge(xs, l2))
        else Cons(y, merge(l1, ys))
      case _ => l1 ++ l2
    }
  } ensuring { res =>
    isSorted(res) &&
    res.size == l1.size + l2.size &&
    bag(res) == bag(l1) ++ bag(l2)
  }

  def split(list: List[BigInt]): (List[BigInt], List[BigInt]) = {
    require(list.size > 1)
    decreases(list)
    list match {
      case Cons(x, xs) if xs.size <= 2 =>
        (List(x), xs)
      case Cons(x1, Cons(x2, xs)) =>
        val (s1, s2) = split(xs)
        (Cons(x1, s1), Cons(x2, s2))
    }
  } ensuring { res =>
    res._1.size + res._2.size == list.size &&
    res._1.size > 0 &&
    res._2.size > 0 &&
    bag(res._1) ++ bag(res._2) == bag(list)
  }

  def mergeSort(list: List[BigInt]): List[BigInt] = {
    decreases(list.size)
    list match {
      case Cons(_, Cons(_, _)) =>
        val (s1, s2) = split(list)
        merge(mergeSort(s1), mergeSort(s2))
      case _ => list
    }
  } ensuring { res =>
    isSorted(res) &&
    res.size == list.size &&
    bag(res) == bag(list)
  }
}
