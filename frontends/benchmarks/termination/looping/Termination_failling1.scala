/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Termination {
  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def looping1(list: List) : Int = looping2(list)

  def looping2(list: List) : Int = looping1(list)

  def calling1(list: List, b: Boolean) : Int = if(b) calling2(list) else looping1(list)

  def calling2(list: List) : Int = list match {
    case Cons(head, tail) => calling1(tail, true)
    case Nil() => 0
  }

  def ok(list: List) : Int = 0
}

// vim: set ts=4 sw=4 et:
