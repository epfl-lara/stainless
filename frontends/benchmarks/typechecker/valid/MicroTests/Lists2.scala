/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless.proof._

object Lists2 {
  sealed abstract class List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def forall[T](list: List[T], f: T => Boolean): Boolean = {
    decreases(list)
    list match {
      case Cons(head, tail) => f(head) && forall(tail, f)
      case Nil() => true
    }
  }

  def positive(list: List[Int]): Boolean = {
    decreases(list)
    list match {
      case Cons(head, tail) => if (head < 0) false else positive(tail)
      case Nil() => true
    }
  }

  def positive_lemma(list: List[Int]): Boolean = {
    positive(list) == forall(list, (x: Int) => x >= 0)
  }

  def positive_lemma_induct(list: List[Int]): Boolean = {
    decreases(list)
    positive_lemma(list) because (list match {
      case Nil() => true
      case Cons(head, tail) => positive_lemma_induct(tail)
    })
  }.holds

  def remove[T](list: List[T], e: T) : List[T] = {
    decreases(list)
    list match {
      case Nil() => Nil()
      case Cons(x, xs) if x == e => remove(xs, e)
      case Cons(x, xs)           => Cons(x, remove(xs, e))
    }
  } //ensuring { (res: List[T]) => forall(res, (x : T) => x != e) }

  def remove_lemma[T](list: List[T], e: T): Boolean = {
    forall(remove(list, e), (x : T) => x != e)
  }

  def remove_lemma_induct[T](list: List[T], e: T): Boolean = {
    decreases(list)
    remove_lemma(list, e) because (list match {
      case Nil() => true
      case Cons(head, tail) => remove_lemma_induct(tail, e)
    })
  }.holds
}

// vim: set ts=4 sw=4 et:
