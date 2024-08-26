package stainless.lang

import stainless.annotation.*
import stainless.lang.*

object Ensures {
  /* `ensures` is an `ensuring` property for first-class functions. */

  // For performance, we hide forall with @opaque 
  @ghost @opaque @library
  def ensures[A,B](f: A => B, post: (A, B) => Boolean): Boolean = {
    forall[A]((a: A) => post(a, f(a)))
  }

  // We instantiate it explicitly with `ensuresOf` on a given argument
  @ghost @opaque @library
  def ensuresOf[A,B](f: A => B, post: (A, B) => Boolean)(a: A): Unit = {
    require(ensures(f, post))
    unfold(ensures(f,post))
  }.ensuring(_ => post(a, f(a)))

  /* To establish ensures(f,post), create a function with this as postcondition and unfold
     the ensures, e.g.

    @ghost @opaque
    def incIncreasing: Unit = {
      unfold(ensures(inc, increasing))
    }.ensuring(_ => ensures(inc, increasing))

   */

  // Larger arities

  @ghost @opaque @library
  def ensures2[A1,A2,B](f: (A1,A2) => B, post: (A1, A2, B) => Boolean): Boolean = {
    forall[A1,A2]((a1: A1, a2: A2) => post(a1, a2, f(a1,a2)))
  }
  @ghost @opaque @library
  def ensures2of[A1,A2,B](f: (A1,A2) => B, post: (A1, A2, B) => Boolean)(a1: A1, a2: A2): Unit = {
    require(ensures2[A1,A2,B](f, post))
    unfold(ensures2[A1,A2,B](f,post))
  }.ensuring(_ => post(a1, a2, f(a1,a2)))

  @ghost @opaque @library
  def ensures3[A1,A2,A3,B](f: (A1,A2,A3) => B, 
                           post: (A1, A2, A3, B) => Boolean): Boolean = {
    forall[A1,A2,A3]((a1: A1, a2: A2, a3: A3) => post(a1, a2, a3, f(a1,a2,a3)))
  }
  @ghost @opaque @library
  def ensures3of[A1,A2,A3,B](f: (A1,A2,A3) => B, post: (A1, A2, A3, B) => Boolean)
                            (a1: A1, a2: A2, a3: A3): Unit = {
    require(ensures3(f, post))
    unfold(ensures3(f,post))
  }.ensuring(_ => post(a1, a2, a3, f(a1,a2,a3)))

  @ghost @opaque @library
  def ensures4[A1,A2,A3,A4,B](f: (A1,A2,A3,A4) => B, 
                              post: (A1, A2, A3, A4, B) => Boolean): Boolean = {
    forall[A1,A2,A3,A4]((a1: A1, a2: A2, a3: A3, a4: A4) => post(a1, a2, a3, a4, f(a1,a2,a3,a4)))
  }
  @ghost @opaque @library
  def ensures4of[A1,A2,A3,A4,B](f: (A1,A2,A3,A4) => B, 
                                post: (A1, A2, A3, A4, B) => Boolean)
                                (a1: A1, a2: A2, a3: A3, a4: A4): Unit = {
    require(ensures4(f, post))
    unfold(ensures4(f,post))
  }.ensuring(_ => post(a1, a2, a3, a4, f(a1,a2,a3,a4)))

}
