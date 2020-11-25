/* Copyright 2009-2021 EPFL, Lausanne */

object Overrides {
  abstract class A {
    def x(a: Int): Int
  }

  abstract class B extends A {
    def x(a: Int) = {
      require(a > 0)
      42
    }
  }

  case class C(c: Int) extends B {
    override def x(i: Int) = {
      require(i >= 0)
      if (i == 0) 0
      else c + x(i-1)
    }
  }

  case class D() extends B
}
