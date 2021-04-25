/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.monads.predicate

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Predicate {

  def exists[A](p: A => Boolean): Boolean = !forall((a: A) => !p(a))

  // Monadic bind
  @inline
  def flatMap[A,B](p: A => Boolean, f: A => (B => Boolean)): B => Boolean = {
    (b: B) => exists[A](a => p(a) && f(a)(b))
  }

  // All monads are also functors, and they define the map function
  @inline
  def map[A,B](p: A => Boolean, f: A => B): B => Boolean = {
    (b: B) => exists[A](a => p(a) && f(a) == b)
  }

  /*
  @inline
  def >>=[B](f: A => Predicate[B]): Predicate[B] = flatMap(f)

  @inline
  def >>[B](that: Predicate[B]) = >>= ( _ => that )

  @inline
  def withFilter(f: A => Boolean): Predicate[A] = {
    Predicate { a => p(a) && f(a) }
  }
  */

  def equals[A](p: A => Boolean, that: A => Boolean): Boolean = {
    forall[A](a => p(a) == that(a))
  }

  def test[A,B,C](p: A => Boolean, f: A => B, g: B => C): Boolean = {
    equals[C](map[B,C](map[A,B](p, f), g), map[A,C](p, (a: A) => g(f(a))))
  }.holds

  /* Disabled
   * Nested quantification is not really a supported feature anyway...
  def testInt(p: BigInt => Boolean, f: BigInt => BigInt, g: BigInt => BigInt): Boolean = {
    equals(map(map(p, f), g), map(p, (x: BigInt) => g(f(x))))
  }.holds
  */
}

