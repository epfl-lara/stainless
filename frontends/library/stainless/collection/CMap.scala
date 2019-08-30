/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.collection

import stainless.annotation._

@library
case class CMap[A, B](f: A => B) {
  def apply(k: A): B = f(k)

  def updated(k: A, v: B): CMap[A, B] =
    CMap((x: A) => if (x == k) v else f(x))

  def getOrElse(k: A, v: B): B = f(k)

  def contains(k: A): Boolean = true
}
