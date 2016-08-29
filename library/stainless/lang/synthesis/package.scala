/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

import scala.language.implicitConversions
import scala.annotation.implicitNotFound

package object synthesis {
  @ignore
  private def noImpl = throw new RuntimeException("Synthesis construct implementation not supported")

  @ignore
  def choose[A](predicate: A => Boolean): A = noImpl
  @ignore
  def choose[A, B](predicate: (A, B) => Boolean): (A, B) = noImpl
  @ignore
  def choose[A, B, C](predicate: (A, B, C) => Boolean): (A, B, C) = noImpl
  @ignore
  def choose[A, B, C, D](predicate: (A, B, C, D) => Boolean): (A, B, C, D) = noImpl
  @ignore
  def choose[A, B, C, D, E](predicate: (A, B, C, D, E) => Boolean): (A, B, C, D, E) = noImpl      

  @ignore
  def ???[T]: T = noImpl

  @ignore
  def ?[T](e1: T): T = if(???[Boolean]) e1 else ???[T]

  @ignore
  def ?[T](e1: T, es: T*): T = noImpl

  // Repair with Holes
  @ignore
  def ?![T](es: Any*): T = noImpl

  @ignore
  def withOracle[A, R](body: Oracle[A] => R): R = noImpl

}
