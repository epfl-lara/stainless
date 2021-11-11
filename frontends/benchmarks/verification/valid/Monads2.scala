/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Monads2 {
  sealed abstract class Option[T]
  case class Some[T](t: T) extends Option[T]
  case class None[T]() extends Option[T]

  def flatMap[T,U](opt: Option[T], f: T => Option[U]): Option[U] = opt match {
    case Some(x) => f(x)
    case None() => None()
  }

  def add[T](o1: Option[T], o2: Option[T]): Option[T] = o1 match {
    case Some(x) => o1
    case None() => o2
  }

  def associative_law[T,U,V](opt: Option[T], f: T => Option[U], g: U => Option[V]): Boolean = {
    flatMap(flatMap(opt, f), g) == flatMap(opt, (x: T) => flatMap(f(x), g))
  }.holds

  def left_unit_law[T,U](x: T, f: T => Option[U]): Boolean = {
    flatMap(Some(x), f) == f(x)
  }.holds

  def right_unit_law[T,U](opt: Option[T]): Boolean = {
    flatMap(opt, (x: T) => Some[T](x)) == opt
  }.holds

  def flatMap_zero_law[T,U](none: None[T], f: T => Option[U]): Boolean = {
    flatMap(none, f) == None[U]()
  }.holds

  def flatMap_to_zero_law[T,U](opt: Option[T]): Boolean = {
    flatMap(opt, (x: T) => None[U]()) == None[U]()
  }.holds

  def add_zero_law[T](opt: Option[T]): Boolean = {
    add(opt, None[T]()) == opt
  }.holds

  def zero_add_law[T](opt: Option[T]): Boolean = {
    add(None[T](), opt) == opt
  }.holds
}

// vim: set ts=4 sw=4 et:
