/* Copyright 2009-2014 EPFL, Lausanne */

object Field2 {

  abstract sealed class A
  case class B(length: Int) extends A

  def foo(): Int = {
    val b = B(3)
    b.length
  } ensuring(_ == 3)

}
