/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object MergeSortTermination {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = {
    decreases(l)
    l match {
      case Nil()       => BigInt(0)
      case Cons(x, xs) => 1 + size(xs)
    }
  } ensuring (res => res >= 0)

  def length(l: List): BigInt = {
    decreases(l)
    l match {
      case Nil()       => BigInt(0)
      case Cons(x, xs) => 1 + length(xs)
    }
  } ensuring (res => res >= 0 && res == size(l))

  def split(l: List, n: BigInt): (List, List) = {
    require(n >= 0 && n <= size(l))
    decreases(l)
    if (n <= 0) (Nil(), l)
    else
      l match {
        case Nil() => (Nil(), l)
        case Cons(x, xs) => {
          val (fst, snd) = split(xs, n - 1)
          (Cons(x, fst), snd)
        }
      }
  } ensuring (res => size(res._2) == size(l) - n && size(res._1) == n)

  def merge(l1: List, l2: List): List = {
    decreases(l1, l2)
    l2 match {
      case Nil() => l1
      case Cons(x, xs) =>
        l1 match {
          case Nil() => l2
          case Cons(y, ys) =>
            if (y < x)
              Cons(y, merge(ys, l2))
            else
              Cons(x, merge(l1, xs))
        }
    }
   } ensuring (res => size(l1) + size(l2) == size(res))

  def mergeSort(l: List): List = {
    decreases(size(l))
    l match {
      case Nil()          => l
      case Cons(x, Nil()) => l
      case _ =>
        val (fst, snd) = split(l, length(l) / 2)
        merge(mergeSort(fst), mergeSort(snd))
    }
  } ensuring (res => size(res) == size(l))
}
