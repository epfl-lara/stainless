/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Existentials {

  def exists[A](p: A => Boolean): Boolean = !forall((x: A) => !p(x))

  def check1(y: BigInt, p: BigInt => Boolean) : Boolean = {
    p(y) == exists((y1:BigInt) => p(y1))
  }.holds

  /*
  def check2(y: BigInt, p: BigInt => Boolean) : Boolean = {
    p(y) ==> exists((y1:BigInt) => p(y1))
  }.holds
  */
}
