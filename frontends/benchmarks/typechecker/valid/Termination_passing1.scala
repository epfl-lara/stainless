/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Termination {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def f1(list: List) : Int = {
    decreases(list, 1)
    f2(list)
  }

  def f2(list: List) : Int = {
    decreases(list, 0)
    list match {
      case Cons(head, tail) => f1(tail)
      case Nil() => 0
    }
  }

  def f3(list: List, b: Boolean) : Int = {
    decreases(list, 2)
    if(b) f4(list) else f1(list)
  }

  def f4(list: List) : Int = {
    decreases(list, 0)
    list match {
      case Cons(head, tail) => f3(tail, true)
      case Nil() => 0
    }
  }
}

// vim: set ts=4 sw=4 et:
