package sortconcat

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._

object SortingnConcatBuggy {

  sealed abstract class LList {
    @inline
    def isEmpty: Boolean = this == SNil()

    lazy val tail: LList = {
      require(!isEmpty)
      this match {
        case SCons(_, tailFun) => tailFun()
      }
    }

    def size: BigInt = {
      this match {
        case c @ SCons(_, _) =>
          1 + (c.tail*).size
        case SNil() =>
          BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  private case class SCons(x: BigInt, tailFun: () => LList) extends LList
  private case class SNil() extends LList

  sealed abstract class List[T] {
    def size: BigInt = {
      this match {
        case Nil()      => BigInt(0)
        case Cons(_, t) => 1 + t.size
      }
    } ensuring (_ >= 0)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

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
  } ensuring (res => res.size == l.size && steps <= 15 * l.size + 2)

  def sort(l: List[BigInt]): LList = {
    pullMin(l) match {
      case Cons(x, xs) =>
        // here, x is the minimum
        SCons(x, () => sort(xs)) // sorts lazily only if needed
      case _ =>
        SNil()
    }
  } ensuring (res => res.size == l.size && steps <= 15 * l.size + 9)

  def concat(l1: List[BigInt], l2: LList): LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, () => concat(xs, l2))
      case Nil()       => l2
    }
  } ensuring (res => steps <= 6)

  def kthMin(l: LList, k: BigInt): BigInt = {
    require(k >= 1)
    l match {
      case c @ SCons(x, _) =>
        if (k == 1) x
        else
          kthMin(c.tail, k - 1)
      case SNil() => BigInt(0)
    }
  } ensuring (_ => steps <= k + 3)
}