/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._

/**
* A lazy selection sorting algorithm that allows accessing the kth minimum
* in O(k.n) time, where `n` is the number of elements in the list.
* See file BottomUpMergeSort for a more optimal algorithm for accessing
* the kth element.
**/
object LazySelectionSort {

  sealed abstract class LList
  case class SCons(x: BigInt, tailFun: Stream) extends LList
  case class SNil() extends LList
  case class Stream(lfun: () => LList) {
    lazy val list: LList = lfun()
  }

  def pullMin(l: List[BigInt]): List[BigInt] = {
    l match {
      case Nil() => l
      case Cons(x, xs) =>
        pullMin(xs) match {
          case Nil() => Cons(x, Nil())
          case nxs @ Cons(y, ys) =>
            if (x <= y) Cons(x, nxs)
            else Cons(y, Cons(x, ys))
        }
    }
  } ensuring(res => res.size <= l.size)

  def sort(l: List[BigInt]): LList = {
    decreases(l.size)
    pullMin(l) match {
      case Cons(x, xs) =>
        // here, x is the minimum
        SCons(x, Stream(() => sort(xs))) // sorts lazily only if needed
      case _ =>
        SNil()
    }
  }

  // a lazy concat method
  def concat(l1: List[BigInt], l2: LList) : LList = {
    decreases(l1)
    l1 match {
      case Cons(x, xs) => SCons(x, Stream(() => concat(xs, l2)))
      case Nil() => SNil()
    }
  }

  // k-th min accompanying the lazy selection sort
  def kthMin(l: Stream, k: BigInt): BigInt = {
    require(k >= 1)
    l.list match {
      case SCons(x, xs) =>
        if (k == 1) x
        else
          kthMin(xs, k - 1)
      case SNil() => BigInt(0)
    }
  }
}
