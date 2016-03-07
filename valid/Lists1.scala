/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.proof._
import leon.collection._
import leon.annotation._

object Lists1 {

  def exists[T](list: List[T], f: T => Boolean): Boolean = list match {
    case Cons(head, tail) => f(head) || exists(tail, f)
    case Nil() => false
  }

  def forall[T](list: List[T], f: T => Boolean): Boolean = list match {
    case Cons(head, tail) => f(head) && forall(tail, f)
    case Nil() => true
  }

  def exists_lemma[T](list: List[T], f: T => Boolean): Boolean = {
    exists(list, f) == !forall(list, (x: T) => !f(x))
  }

  def exists_lemma_induct[T](list: List[T], f: T => Boolean): Boolean = {
    exists_lemma(list, f) because (list match {
      case Nil() => true
      case Cons(head, tail) => exists_lemma_induct(tail, f)
    })
  }.holds 

}

// vim: set ts=4 sw=4 et:
