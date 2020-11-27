/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Subtyping2 {

  sealed abstract class List
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
