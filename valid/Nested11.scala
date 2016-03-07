/* Copyright 2009-2016 EPFL, Lausanne */

object Nested11 {

  abstract class A
  case class B(b: Int) extends A

  def foo(i: Int): Int = {
    val b: A = B(3)
    def rec1(j: Int) = b match {
      case B(b) => i + j + b
    }
    rec1(2)
  } ensuring(i + 5 == _)

}
