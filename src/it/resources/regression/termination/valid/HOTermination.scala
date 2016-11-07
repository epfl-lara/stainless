/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object HOTermination {
  abstract class List[T]
  case class Cons[T](head: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  abstract class Option[T]
  case class Some[T](value: T) extends Option[T]
  case class None[T]() extends Option[T]

  def map[A,B](list: List[A], f: A => B): List[B] = list match {
    case Cons(head, tail) => Cons(f(head), map(tail, f))
    case Nil() => Nil()
  }

  abstract class Expr
  case class Invocation(e: Expr, args: List[Expr]) extends Expr
  case class Addition(e1: Expr, e2: Expr) extends Expr
  case class Variable(i: Int) extends Expr

  def transform(e: Expr, f: Expr => Option[Expr]): Expr = {
    f(e) match {
      case Some(newExpr) => newExpr
      case None() => e match {
        case Invocation(c, args) =>
          val newC = transform(c, f)
          val newArgs = map(args, (x: Expr) => transform(x, f))
          Invocation(newC, newArgs)
        case Addition(e1, e2) =>
          Addition(transform(e1, f), transform(e2, f))
        case Variable(i) => e
      }
    }
  }
}

// vim: set ts=4 sw=4 et:
