/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.proof._

object Lists4 {
  abstract class List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  def map[F,T](list: List[F], f: F => T): List[T] = list match {
    case Cons(head, tail) => Cons(f(head), map(tail, f))
    case Nil() => Nil()
  }

  def map_lemma[A,B,C](list: List[A], f: A => B, g: B => C): Boolean = {
    map(list, (x: A) => g(f(x))) == map(map(list, f), g)
  }

  def map_lemma_induct[D,E,F](list: List[D], f: D => E, g: E => F): Boolean = {
    map_lemma(list, f, g) because (list match {
      case Nil() => true
      case Cons(head, tail) => map_lemma_induct(tail, f, g)
    })
  }.holds

}

// vim: set ts=4 sw=4 et:
