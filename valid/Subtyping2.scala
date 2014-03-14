/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Test {

  abstract class List
  case class Nil() extends List
  case class Cons(head: Int, tail: List) extends List

  def test(x: List): Nil = {
    x match {
      case Cons(_, tail) => test(tail)
      case Nil() => Nil()
    }
  } ensuring((res: Nil) => isEmpty(res))

  def isEmpty(x: List): Boolean = x match {
    case Nil() => true
    case _ => false
  }

}
