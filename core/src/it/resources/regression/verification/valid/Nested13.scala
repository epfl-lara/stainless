/* Copyright 2009-2016 EPFL, Lausanne */

object Nested13 {

  abstract class D
  case class E(e: Int) extends D
  case class F(d: D, f: Int) extends D

  def foo(a : Int): Int = {

    def rec1(d: D, j: Int): Int = d match {
      case E(e) => j + e + a
      case F(dNext, f) => f + rec1(dNext, j)
    }

    def rec2(d: D, i : Int) : Int = d match {
      case E(e) => e
      case F(dNext, f) => rec1(d, i)
    }

    rec2(F(E(2), 3), 0)
  } ensuring(a + 5 == _)
}
