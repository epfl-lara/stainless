/* Copyright 2009-2016 EPFL, Lausanne */

package leon.monads.predicate

import leon.collection._
import leon.lang._
import leon.annotation._

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
    equals(map(map(p, f), g), map(p, (a: A) => g(f(a))))
  }.holds

  /* Disabled
   * Nested quantification is not really a supported feature anyway...
  def testInt(p: BigInt => Boolean, f: BigInt => BigInt, g: BigInt => BigInt): Boolean = {
    equals(map(map(p, f), g), map(p, (x: BigInt) => g(f(x))))
  }.holds
  */
}

