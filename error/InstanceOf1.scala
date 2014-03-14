/* Copyright 2009-2014 EPFL, Lausanne */

object InstanceOf1 {

  abstract class A
  case class B(i: Int) extends A
  case class C(i: Int) extends A

  abstract class Z
  case class Y(i: Int) extends Z

  def foo(): Int = {
    //require(3.isInstanceOf[Int])
    val b: A = B(2)
    if(b.isInstanceOf[Y])
      0
    else
      -1
  } ensuring(_ == 0)

  def bar(): Int = foo()

}

// vim: set ts=4 sw=4 et:
