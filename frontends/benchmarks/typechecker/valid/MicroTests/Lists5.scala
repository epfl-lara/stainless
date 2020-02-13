/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._
import stainless.proof._
import stainless.collection._

object Lists5 {
  sealed abstract class Option[T]
  case class Some[T](value: T) extends Option[T]
  case class None[T]() extends Option[T]

  def find[T](f: T => Boolean, list: List[T]): Option[T] = {
    decreases(list)
    list match {
      case Cons(head, tail) => if (f(head)) Some(head) else find(f, tail)
      case Nil() => None()
    }
  }

  def exists[T](f: T => Boolean, list: List[T]): Boolean = {
    decreases(list)
    list match {
      case Cons(head, tail) => f(head) || exists(f, tail)
      case Nil() => false
    }
  }

  def equivalence_lemma[T](f: T => Boolean, list: List[T]): Boolean = {
    find(f, list) match {
      case Some(e) => exists(f, list)
      case None() => !exists(f, list)
    }
  }

  def equivalence_lemma_induct[T](f: T => Boolean, list: List[T]): Boolean = {
    decreases(list)
    equivalence_lemma(f, list) because (list match {
      case Cons(head, tail) => equivalence_lemma_induct(f, tail)
      case Nil() => true
    })
  }.holds
}
