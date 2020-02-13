/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import math._

/**
 * Computing the kthe min using a version of merge sort that operates bottom-up.
 * This allows accessing the first element in the sorted list in O(n) time,
 * and kth element in O(kn) time.
 */
object BottomUpMergeSortPrecise {

  @inline
  def max(x:BigInt, y:BigInt) = if (x >= y) x else y

  sealed abstract class List[T] {
    // length is used in the implementation
    val length: BigInt = {
      this match {
        case Nil() => BigInt(0)
        case Cons(h, t) => 1 + t.length
      }
    } ensuring (_ >= 0)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  private sealed abstract class LList {
    def size = this match {
      case SCons(_, _, sz) if sz >= 0 => sz
      case _ => BigInt(0)
    }

    lazy val tail: LList = {
      require(this != SNil())
      this match {
        case SCons(_, tfun, _) => tfun()
      }
    }

    def finite: Boolean = {
      decreases(this.size) // FIXME(measure): Cannot infer measure
      this match {
        case c @ SCons(_, _, sz) =>
          val rear = c.tail
          sz >= 0 && sz == rear.size + 1 && rear.finite
        case _ => true
      }
    }
  }
  private case class SCons(x: BigInt, tailFun: () => LList, sz: BigInt) extends LList
  private case class SNil() extends LList

  @inline
  private val nilStream: () => LList = () => SNil()

  /**
   *
   * this method is a functional implementation of buildheap in linear time.
   */
  private def constructMergeTree(l: List[BigInt], from: BigInt, to: BigInt): (LList, List[BigInt]) = {
    require(from <= to && from >= 0)
    decreases(abs(to-from)) // FIXME(measure): Cannot infer measure
    l match {
      case Nil()           => (SNil(), Nil[BigInt]()) // this case is unreachable
      case Cons(x, tail)  =>
        if(from == to) (SCons(x, nilStream, 1), tail)
        else {
          val mid = (from + to) / 2
          val (lside, midlist) = constructMergeTree(l, from, mid)
          val (rside, rest) = constructMergeTree(midlist, mid + 1, to)
          (merge(lside, rside), rest)
        }
    }
  } ensuring{ res => res._1.finite }

  private def merge(a: LList, b: LList): LList = {
    require(a.finite && b.finite)
    decreases(a.size + b.size) // FIXME(measure): Cannot infer measure
    b match {
      case SNil() => a
      case SCons(x, xs, bsz) =>
        a match {
          case SNil() => b
          case SCons(y, ys, asz) =>
            if (y < x)
              SCons(y, () => merge(b, a.tail), asz + bsz) // here, the order of arguments is changed, the sort is not a stable sort
            else
              SCons(x, () => merge(a, b.tail), asz + bsz)
        }
    }
  } ensuring{res => res.finite }

  /**
   * Takes list of integers and returns a sorted stream of integers.
   * Takes steps linear in the size of the  input since it sorts lazily.
   */
  private def mergeSort(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case _ => constructMergeTree(l, 0, l.length - 1)._1
    }
  } ensuring (res => res.finite)

  private def kthMinRec(l: LList, k: BigInt): BigInt = {
    require(k >= 0)
    decreases(k) // FIXME(measure): Required because measure infered by ChainProcessor ins invalid
    l match {
      case SCons(x, _, _) =>
        if (k == 0) x
        else
          kthMinRec(l.tail, k - 1)
      case SNil() => BigInt(0)
    }
  }

  /**
   * A function that accesses the kth element of a list using lazy sorting.
   */
  def kthMin(l: List[BigInt], k: BigInt): BigInt = {
    require(k >= 0)
    kthMinRec(mergeSort(l), k)
  }
}
