/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.proof._
import leon.collection._

object Lists6 {
  def exists[T](list: List[T], f: T => Boolean): Boolean = {
    list match {
      case Cons(head, tail) => f(head) || exists(tail, f)
      case Nil() => false
    }
  }

  def associative_lemma[T](list: List[T], f: T => Boolean, g: T => Boolean): Boolean = {
    exists(list, (x: T) => f(x) || g(x)) == (exists(list, f) || exists(list, g))
  }

  def associative_lemma_induct[T](list: List[T], f: T => Boolean, g: T => Boolean): Boolean = {
    associative_lemma(list, f, g) because (list match {
      case Cons(head, tail) => associative_lemma_induct(tail, f, g)
      case Nil() => true
    })
  }.holds
}
