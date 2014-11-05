/* Copyright 2009-2014 EPFL, Lausanne */

import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object SearchLinkedList {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def size(list : List) : BigInt = (list match {
    case Nil() => BigInt(0)
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  })

  def firstZero(list : List) : BigInt = (list match {
    case Nil() => BigInt(0)
    case Cons(x, xs) => if (x == 0) BigInt(0) else firstZero(xs) + 1
  }) ensuring (res =>
    res >= 0 && (if (contains(list, 0)) {
      firstZeroAtPos(list, res)
    } else {
      res == size(list)
    }))

  def firstZeroAtPos(list : List, pos : BigInt) : Boolean = {
    list match {
      case Nil() => false
      case Cons(x, xs) => if (pos == BigInt(0)) x == 0 else x != 0 && firstZeroAtPos(xs, pos - 1)
    }
  } 

  def goal(list : List, i : BigInt) : Boolean = {
    if(firstZero(list) == i) {
      if(contains(list, 0)) {
        firstZeroAtPos(list, i)
      } else {
        i == size(list)
      }
    } else {
      true
    }
  }.holds
}
