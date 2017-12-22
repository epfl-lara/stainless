/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package lang

import annotation._

/**
 * Describe a partial function with precondition [[pre]].
 *
 * Do not attempt to create it using the ~>'s companion object's apply method.
 * Instead, use [[PartialFunction.apply]] defined beflow. (Private constructor
 * cannot be expressed in Stainless.)
 */
@library
case class ~>[A,B] /*private*/ (pre: A => Boolean, f: A => B) {
  def apply(a: A): B = {
    require(pre(a))
    f(a)
  }
}

@library
case class ~>>[A,B](pre: A => Boolean, private val f: A => B, post: B => Boolean) {
  require(forall((x: A) => pre(x) ==> post(f(x))))

  def apply(a: A): B = {
    require(pre(a))
    f(a)
  } ensuring(post)
}

@library
object PartialFunction {
  /**
   * Construct an instance of ~> by extracting the precondition (if any) from
   * the given lambda [[f]]. For example,
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
  @ignore
  def apply[A,B](f: A => B): A ~> B = ~>(_ => true, f)
}

