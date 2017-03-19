/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

import scala.language.implicitConversions
import scala.annotation.implicitNotFound

package object synthesis {
  @ignore
  private def noImpl = throw new RuntimeException("Synthesis construct implementation not supported")

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
