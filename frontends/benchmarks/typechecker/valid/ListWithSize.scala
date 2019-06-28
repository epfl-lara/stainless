/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object ListWithSize {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    sealed abstract class IntPairList
    case class IPCons(head: IntPair, tail: IntPairList) extends IntPairList
    case class IPNil() extends IntPairList

    sealed abstract class IntPair
    case class IP(fst: Int, snd: Int) extends IntPair

    // proved with unrolling=0
    def size(l: List) : BigInt = {
      decreases(l)
      l match {
        case Nil() => BigInt(0)
        case Cons(_, t) => 1 + size(t)
      }
    } ensuring(res => res >= 0)

    def iplSize(l: IntPairList) : BigInt = {
      decreases(l)
      l match {
        case IPNil() => BigInt(0)
        case IPCons(_, xs) => 1 + iplSize(xs)
      }
    } ensuring(_ >= 0)

    def zip(l1: List, l2: List) : IntPairList = {
      // try to comment this and see how pattern-matching becomes
      // non-exhaustive and post-condition fails
      require(size(l1) == size(l2))
      decreases(l1)

      l1 match {
        case Nil() => IPNil()
        case Cons(x, xs) => l2 match {
          case Cons(y, ys) => IPCons(IP(x, y), zip(xs, ys))
        }
      }
    } ensuring(iplSize(_) == size(l1))

    def sizeTailRec(l: List) : BigInt = sizeTailRecAcc(l, 0)
    def sizeTailRecAcc(l: List, acc: BigInt) : BigInt = {
     require(acc >= 0)
     decreases(l)
     l match {
       case Nil() => acc
       case Cons(_, xs) => sizeTailRecAcc(xs, acc+1)
     }
    } ensuring(res => res == size(l) + acc)

    def sizesAreEquiv(l: List) : Boolean = {
      size(l) == sizeTailRec(l)
    }.holds

    def content(l: List) : Set[Int] = {
      decreases(l)
      l match {
        case Nil() => Set.empty[Int]
        case Cons(x, xs) => Set(x) ++ content(xs)
      }
    }

    def sizeAndContent(l: List) : Boolean = {
      size(l) == 0 || content(l) != Set.empty[Int]
    }.holds

    def drunk(l : List) : List = {
      decreases(l)
      l match {
        case Nil() => Nil()
        case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
      }
    } ensuring (size(_) == 2 * size(l))

    // proved with unrolling=1
    def funnyCons(x: Int, l: List) : List = (l match {
        case Nil() => Cons(x, Nil())
        case c @ Cons(_,_) => Cons(x, c)
    }) ensuring(size(_) > 0)

    // proved with unrolling=2
    def reverse(l: List) : List = reverse0(l, Nil()) ensuring(content(_) == content(l))
    def reverse0(l1: List, l2: List) : List = {
      decreases(l1)
      l1 match {
        case Nil() => l2
        case Cons(x, xs) => reverse0(xs, Cons(x, l2))
      }
    } ensuring(content(_) == content(l1) ++ content(l2))

    def append(l1 : List, l2 : List) : List = {
      decreases(l1)
      l1 match {
        case Nil() => l2
        case Cons(x,xs) => Cons(x, append(xs, l2))
      }
    } ensuring(content(_) == content(l1) ++ content(l2))

    def nilAppend(@induct l : List) : Boolean = {
      append(l, Nil()) == l
    }.holds

    def appendAssoc(@induct xs : List, ys : List, zs : List) : Boolean = {
      append(append(xs, ys), zs) == append(xs, append(ys, zs))
    }.holds

    def sizeAppend(@induct l1 : List, l2 : List) : Boolean = {
      size(append(l1, l2)) == size(l1) + size(l2)
    }.holds

    // proved with unrolling=4
    def concat(l1: List, l2: List) : List = {
      concat0(l1, l2, Nil()) ensuring(content(_) == content(l1) ++ content(l2))
    }

    def concat0(l1: List, l2: List, l3: List) : List = {
      decreases(l1, l2)
      l1 match {
        case Nil() => l2 match {
          case Nil() => reverse(l3)
          case Cons(y, ys) => {
            concat0(Nil(), ys, Cons(y, l3))
          }
        }
        case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
      }
    } ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))
}
