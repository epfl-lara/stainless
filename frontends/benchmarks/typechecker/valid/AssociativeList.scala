/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object AssociativeList {
  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class List
  case class Cons(head: KeyValuePairAbs, tail: List) extends List
  case class Nil() extends List

  sealed abstract class OptionInt
  case class Some(i: Int) extends OptionInt
  case class None() extends OptionInt

  def domain(l: List): Set[Int] = {
    decreases(l)
    l match {
      case Nil() => Set.empty[Int]
      case Cons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
    }
  }

  def find(l: List, e: Int): OptionInt = {
    decreases(l)
    l match {
      case Nil() => None()
      case Cons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
    }
  }

  def noDuplicates(l: List): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
    }
  }

  def updateAll(l1: List, l2: List): List = {
    decreases(l2)
    l2 match {
      case Nil() => l1
      case Cons(x, xs) => updateAll(updateElem(l1, x), xs)
    }
  } ensuring(domain(_) == domain(l1) ++ domain(l2))

  def updateElem(l: List, e: KeyValuePairAbs): List = {
    decreases(l)
    l match {
      case Nil() => Cons(e, Nil())
      case Cons(KeyValuePair(k, v), xs) => e match {
        case KeyValuePair(ek, ev) => if (ek == k) Cons(KeyValuePair(ek, ev), xs) else Cons(KeyValuePair(k, v), updateElem(xs, e))
      }
    }
  } ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  def readOverWrite(@induct l: List, k1: Int, k2: Int, e: Int) : Boolean = {
    find(updateElem(l, KeyValuePair(k2,e)), k1) == (if (k1 == k2) Some(e) else find(l, k1))
  }.holds
}
