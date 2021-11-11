/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object PositiveMap {

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def positive(list: List): Boolean = list match {
    case Cons(head, tail) => if (head < 0) false else positive(tail)
    case Nil() => true
  }

  def positiveMap_failling_1(f: (Int) => Int, list: List): List = {
    list match {
      case Cons(head, tail) =>
        val fh = f(head)
        val nh = if (fh < -1) 0 else fh
        Cons(nh, positiveMap_failling_1(f, tail))
      case Nil() => Nil()
    }
  } ensuring { res => positive(res) }
}

// vim: set ts=4 sw=4 et:
