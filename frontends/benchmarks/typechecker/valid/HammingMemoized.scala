/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import math._

/**
 * A memoized version of the implementation of Hamming problem shown in
 * section 4.3 of Type-based allocation analysis for Co-recursion.
 */
object Hamming {
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList {
    @extern
    override def toString: String = {
      if(tail == Nil()) x.toString
      else x.toString + "," + tail.toString
    }
  }
  case class Nil() extends IList {
    @extern
    override def toString = ""
  }

  case class Data(v: BigInt, i2: BigInt, i3: BigInt, i5: BigInt)

  def ham(n: BigInt): Data = {
    require(n >= 0)
    decreases(abs(n))
    if(n == BigInt(0)) Data(1, 0, 0, 0)
    else {
      val Data(x, i2, i3, i5) = ham(n-1)
      val a = ham(i2).v * 2
      val b = ham(i3).v * 3
      val c = ham(i5).v * 5
      val (v, ni, nj, nk) = threeWayMerge(a, b, c, i2, i3, i5)
      Data(v, ni, nj, nk)
    }
  } ensuring(res =>  res.i2 <= n && res.i3 <= n && res.i5 <= n &&
      res.i3 >= 0 && res.i5 >= 0 && res.i2 >= 0)

  /**
   * Returns a list of hamming numbers upto 'n'
   */
  def hammingList(n: BigInt): IList = {
    require(n >= 0)
    decreases(n)
    if(n == 0) {
        Cons( ham(n).v, Nil())
    } else {
      val tailRes =  hammingList(n-1)
      Cons( ham(n).v, tailRes)
    }
  }

  @inline
   def threeWayMerge(a: BigInt, b: BigInt, c: BigInt, i2: BigInt, i3: BigInt, i5: BigInt) = {
      if(a == b && b == c)      (a, i2 + 1, i3 + 1, i5 + 1)
      else if(a == b && a < c)  (a, i2 + 1, i3 + 1, i5    )
      else if(a == c && a < b)  (a, i2 + 1, i3    , i5 + 1)
      else if(b == c && b < a)  (b, i2    , i3 + 1, i5 + 1)
      else if(a < b && a < c)   (a, i2 + 1, i3    , i5    )
      else if(b < c && b < a)   (b, i2    , i3 + 1, i5    )
      else/*if(c < a && c < b)*/(c, i2    , i3    , i5 + 1)
   }
}
