/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Generics1 {
  abstract class List[T]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[B]() extends List[B]

  def size[T](l: List[T]): BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1+size(t)
  })ensuring { _ >= 0 }

  def content[T](l: List[T]): Set[T] = l match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ content(t)
  }

  def insert[T](a: T, l: List[T]): List[T] = {
    Cons(a, l)
  } ensuring { res => (size(res) == size(l) + 1) && (content(res) == content(l) ++ Set(a))}
}
