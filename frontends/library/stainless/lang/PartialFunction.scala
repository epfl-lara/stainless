/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package lang

import annotation._
import stainless.lang.StaticChecks._

/**
 * Describe a partial function with precondition `pre`.
 *
 * Do not attempt to create it using the ~>'s companion object's apply method.
 * Instead, use `PartialFunction$.apply` defined below. (Private constructor
 * cannot be expressed in Stainless.)
 */
@library
case class ~>[A, B] private[stainless](pre: A => Boolean, private val f: A => B) {
  def apply(a: A): B = {
    require(pre(a))
    f(a)
  }
}

@library
case class ~>>[A, B](private val f: A ~> B, post: B => Boolean) {
  require(forall((x: A) => f.pre(x) ==> post(f(x))))

  lazy val pre = f.pre

  def apply(a: A): B = {
    require(pre(a))
    f(a)
  } ensuring(post)
}

@library
object PartialFunction {
  /**
   * Construct an instance of ~> by extracting the precondition (if any) from
   * the given lambda `f`. For example,
   *
   *   PartialFunction{ (x: A) => require(pre(x)); body(x) }
   *
   * is converted into
   *
   *    ~>(
   *      { (x: A) => pre(x) },
   *      { (x: A) => assume(pre(x)); body(x) }
   *    )
   */
  @extern
  def apply[A, B](f: A => B): A ~> B = {
    ~>(x => scala.util.Try(f(x)).isSuccess, f)
  }

  @extern
  def apply[A, B, C](f: (A, B) => C): (A, B) ~> C = {
    ~>(p => scala.util.Try(f.tupled(p)).isSuccess, f.tupled)
  }

  @extern
  def apply[A, B, C, D](f: (A, B, C) => D): (A, B, C) ~> D = {
    ~>(p => scala.util.Try(f.tupled(p)).isSuccess, f.tupled)
  }

}

