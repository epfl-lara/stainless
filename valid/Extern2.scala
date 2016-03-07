/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.annotation._

object Extern2 {
  @extern
  def plop(a: BigInt): BigInt = {
    a + scala.math.abs(-3)
  } ensuring {
    _ > 0
  }

  def test(b: BigInt): BigInt = {
    plop(if (b <= 0) -b+1 else b)
  } ensuring {
    _ > 0
  }

  def test2 = test(42)
  def test3 = test(-2)
}
