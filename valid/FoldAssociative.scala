/* Copyright 2009-2015 EPFL, Lausanne */

import leon._
import leon.lang._

object FoldAssociative {

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Option
  case class Some(x: Int) extends Option
  case class None() extends Option

  def foldRight[A](list: List, state: A, f: (Int, A) => A): A = list match {
    case Cons(head, tail) =>
      val tailState = foldRight(tail, state, f)
      f(head, tailState)
    case Nil() => state
  }

  def take(list: List, count: Int): List = {
    require(count >= 0)
    list match {
      case Cons(head, tail) if count > 0 => Cons(head, take(tail, count - 1))
      case _ => Nil()
    }
  }

  def drop(list: List, count: Int): List = {
    require(count >= 0)
    list match {
      case Cons(head, tail) if count > 0 => drop(tail, count - 1)
      case _ => list
    }
  }

  def append(l1: List, l2: List): List = {
    l1 match {
      case Cons(head, tail) => Cons(head, append(tail, l2))
      case Nil() => l2
    }
  }

  def lemma_split(list: List, x: Int): Boolean = {
    require(x >= 0)
    val f = (x: Int, s: Int) => x + s
    val l1 = take(list, x)
    val l2 = drop(list, x)
    foldRight(list, 0, f) == foldRight(l1, foldRight(l2, 0, f), f)
  }

  def lemma_split_induct(list: List, x: Int): Boolean = {
    require(x >= 0)
    val f = (x: Int, s: Int) => x + s
    val l1 = take(list, x)
    val l2 = drop(list, x)
    lemma_split(list, x) && (list match {
      case Cons(head, tail) if x > 0 =>
        lemma_split_induct(tail, x - 1)
      case _ => true
    })
  }.holds

  def lemma_reassociative(list: List, x: Int): Boolean = {
    require(x >= 0)
    val f = (x: Int, s: Int) => x + s
    val l1 = take(list, x)
    val l2 = drop(list, x)

    foldRight(list, 0, f) == foldRight(l1, 0, f) + foldRight(l2, 0, f)
  }

  def lemma_reassociative_induct(list: List, x: Int): Boolean = {
    require(x >= 0)
    val f = (x: Int, s: Int) => x + s
    val l1 = take(list, x)
    val l2 = drop(list, x)
    lemma_reassociative(list, x) && (list match {
      case Cons(head, tail) if x > 0 =>
        lemma_reassociative_induct(tail, x - 1)
      case _ => true
    })
  }.holds

  def lemma_reassociative_presplit(l1: List, l2: List): Boolean = {
    val f = (x: Int, s: Int) => x + s
    val list = append(l1, l2)
    foldRight(list, 0, f) == foldRight(l1, 0, f) + foldRight(l2, 0, f)
  }

  def lemma_reassociative_presplit_induct(l1: List, l2: List): Boolean = {
    val f = (x: Int, s: Int) => x + s
    val list = append(l1, l2)
    lemma_reassociative_presplit(l1, l2) && (l1 match {
      case Cons(head, tail) =>
        lemma_reassociative_presplit_induct(tail, l2)
      case Nil() => true
    })
  }.holds

}
