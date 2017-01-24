/* Copyright 2009-2016 EPFL, Lausanne */

object Nested12 {

  abstract class A
  case class B(b: Int) extends A

  def foo(i: Int): Int = {
    val b: A = B(3)
    def rec1(a: A, j: Int, j2: Int) = a match {
      case B(b) => i + j + j2 + b
    }
    def rec2(a: A, k: Int) = a match {
      case B(b) => rec1(a, b, k)
    }
    rec2(b, 2)
  } ensuring(i + 8 == _)

}
