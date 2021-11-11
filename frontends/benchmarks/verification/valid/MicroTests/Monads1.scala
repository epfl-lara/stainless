/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Monads1 {
  sealed abstract class Try[T]
  case class Success[T](value: T) extends Try[T]
  case class Failure[T](error: Int) extends Try[T]

  def flatMap[T,U](t: Try[T], f: T => Try[U]): Try[U] = t match {
    case Success(value) => f(value)
    case fail @ Failure(error) => Failure(error)
  }

  def associative_law[T,U,V](t: Try[T], f: T => Try[U], g: U => Try[V]): Boolean = {
    flatMap(flatMap(t, f), g) == flatMap(t, (x: T) => flatMap(f(x), g))
  }.holds

  def left_unit_law[T,U](x: T, f: T => Try[U]): Boolean = {
    flatMap(Success(x), f) == f(x)
  }.holds

  def right_unit_law[T,U](t: Try[T]): Boolean = {
    flatMap(t, (x: T) => Success[T](x)) == t
  }.holds
}
