/* Copyright 2009-2014 EPFL, Lausanne */

object InstanceOf1 {

  abstract class A
  case class B(i: Int) extends A
  case class C(i: Int) extends A

  def foo(): Int = {
    require(C(3).isInstanceOf[C])
    val b: A = B(2)
    if(b.isInstanceOf[B])
      0
    else
      -1
  } ensuring(_ == 0)

  def bar(): Int = foo()

}
