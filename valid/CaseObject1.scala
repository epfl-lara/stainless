/* Copyright 2009-2014 EPFL, Lausanne */

object CaseObject1 {

  abstract sealed class A
  case class B(size: Int) extends A
  case object C extends A

  def foo(): A = {
    C
  }

  def foo1(a: A): A = a match {
    case C => a
    case B(s) => a 
  }

  def foo2(a: A): A = a match {
    case c @ C => c
    case B(s) => a
  }

}
