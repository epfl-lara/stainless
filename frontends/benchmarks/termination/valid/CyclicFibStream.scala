/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import collection._

object ZipWithAndFibStream {
  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  case class SCons(x: BigInt, tailFun: () => SCons) {
    lazy val tail = tailFun()
  }

  /**
   * A generic higher-order `zipWithFun` function.
   */
  private def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        SCons(f(x, y), () => zipWithFun(f, xs.tail, ys.tail))
    }
  }

  def nthElem(n: BigInt, s: SCons): BigInt = {
    require(n >= 0)
    if (n == 0) s.x
    else {
      nthElem(n - 1, s.tail)
    }
  }

  /**
   * Using a `zipWithFun` function to implement a fibonacci stream.
   */
  val fibstream: SCons = SCons(0, () => SCons(1, () => {
    zipWithFun(_ + _, this.fibstream, this.fibstream.tail)
  }))

  def nthFib(n: BigInt) = {
    require(n >= 0)
    nthElem(n, fibstream)
  }
}
