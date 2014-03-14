/* Copyright 2009-2014 EPFL, Lausanne */


object MyTuple4 {

  abstract class A
  case class B(i: Int) extends A
  case class C(a: A) extends A

  def foo(): Int = {
    val t = (1, (C(B(4)), 2), 3)
    val (a1, (C(B(x)), a2), a3) = t
    x
  } ensuring( _ == 4)

}
