/* Copyright 2009-2018 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._

object DigitObject {
  sealed abstract class Digit
  case class Zero() extends Digit {
    @extern
    override def toString = "0"
  }
  case class One() extends Digit {
    @extern
    override def toString = "1"
  }
}

import DigitObject._
object LazyNumericalRep {

  sealed abstract class NumList {
    @inline
    val isTip = this == Tip()
    @inline
    val isSpine: Boolean = !isTip

    def size = this match {
      case Spine(_, _, sz) if sz >= 0 => sz
      case _ => BigInt(0)
    }

    def finite: Boolean = {
      decreases(this.size)
      this match {
        case c @ Spine(_, rear, sz) =>
          sz >= 0 && sz > rear.size && rear.finite  //  Note here the exact value of size is not important it should just increase
        case _ => true
      }
    }
  }

  case class Tip() extends NumList
  case class Spine(head: Digit, rear: NumStream, sz: BigInt) extends NumList

  sealed abstract class NumStream {

    def isSusp = this match {
      case _: Susp => true
      case _       => false
    }

    lazy val fval = {
      require(isSusp)
      this match {
        case Susp(f) => f()
      }
    }

    //@inline - inline here crashes Dotty compiler
    def get: NumList = {
      this match {
        case Susp(f) => fval
        case Val(x)  => x
      }
    }

    def size = this.get.size

    def finite: Boolean = this.get.finite
  }
  private case class Val(x: NumList) extends NumStream
  private case class Susp(fun: () => NumList) extends NumStream

  case class Number(digs: NumStream, schedule: List[NumStream]) {
    def valid = digs.finite
  }

  def emptyNum = Number(Val(Tip()), Nil())

  def inc(xs: NumStream): NumList = {
    require(xs.finite)
    xs.get match {
      case Tip() =>
        Spine(One(), xs, BigInt(1))
      case s @ Spine(Zero(), rear, sz) =>
        Spine(One(), rear, sz)
      case s @ Spine(_, _,_) =>
        incLazy(xs)
    }
  }

  def incLazy(xs: NumStream): NumList = {
    require(xs.finite && xs.get.isSpine)
    decreases(xs.size)
    xs.get match {
      case Spine(head, rear, sz) =>
        val carry = One()
        rear.get match {
          case Tip() =>
            Spine(Zero(), Val(Spine(carry, rear, sz)), sz + 1)

          case Spine(Zero(), srearfun, rearsz) =>
            assert(Spine(Zero(), Val(Spine(carry, srearfun, rearsz)), sz).finite)
            Spine(Zero(), Val(Spine(carry, srearfun, rearsz)), sz)

          case s =>
            assert(Spine(Zero(), Susp(() => incLazy(rear)), sz + 1).finite)
            Spine(Zero(), Susp(() => incLazy(rear)), sz + 1)
        }
    }
  } ensuring { res => res.finite && res.size <= xs.size + 1 }

  def incNum(w: Number): (NumStream, List[NumStream]) = {
    require(w.valid)
    val nq = inc(w.digs)
    val nsched = nq match {
      case Spine(Zero(), rear: Susp, _) =>
        Cons(rear, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Val(nq), nsched)
  }

  def Pay(q: NumStream, scheds: List[NumStream]): List[NumStream] = {
    scheds match {
      case c @ Cons(head, rest) =>
        head.get match {
          case Spine(Zero(), rear: Susp, _) => Cons(rear, rest)
          case _                         => rest
        }
      case Nil() => scheds
    }
  }

  /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  def incAndPay(w: Number) = {
    require(w.valid)
    val (q, scheds) = incNum(w)
    val nscheds = Pay(q, scheds)
    Number(q, nscheds)

  } ensuring { res => res.valid }

  def firstDigit(w: Number): Digit = {
    require(!w.digs.get.isTip)
    w.digs.get match {
      case Spine(d, _, _) => d
    }
  }
}
