/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package lang

import annotation._

@library
case class ~>[A,B](pre: A => Boolean, f: A => B) {
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
  // apply((x: A) => require(pre); body) will be converted to
  // ~>((x: A) => pre, (x: A) => unsafe_assume(pre); body)
  
  def apply[A,B](f: A => B): A ~> B = ~>(_ => true, f)
}