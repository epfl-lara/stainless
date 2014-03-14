/* Copyright 2009-2014 EPFL, Lausanne */

object Field1 {

  abstract sealed class A
  case class B(size: Int) extends A

  def foo(): Int = {
    val b = B(3)
    b.size
  } ensuring(_ == 3)

}
