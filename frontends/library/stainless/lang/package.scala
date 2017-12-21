/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import stainless.annotation._
import scala.language.implicitConversions

package object lang {
  import stainless.proof._

  @ignore
  implicit class BooleanDecorations(val underlying: Boolean) {
    def holds : Boolean = {
      underlying
    } ensuring {
      (res: Boolean) => res
    }

    def holds(becauseOfThat: Boolean) = {
      underlying
    } ensuring {
      (res: Boolean) => becauseOfThat && res
    }

    def ==>(that: => Boolean): Boolean = {
      if (underlying) that else true
    }
  }

  @inline @library def because(b: Boolean) = b

  @ignore def forall[A](p: A => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B](p: (A,B) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C](p: (A,B,C) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C,D](p: (A,B,C,D) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @ignore def forall[A,B,C,D,E](p: (A,B,C,D,E) => Boolean): Boolean = sys.error("Can't execute quantified proposition")

  @ignore def choose[A](predicate: A => Boolean): A = sys.error("Can't execute non-deterministic choose")
  @ignore def choose[A,B](predicate: (A,B) => Boolean): (A,B) = sys.error("Can't execute non-deterministic choose")
  @ignore def choose[A,B,C](predicate: (A,B,C) => Boolean): (A,B,C) = sys.error("Can't execute non-deterministic choose")
  @ignore def choose[A,B,C,D](predicate: (A,B,C,D) => Boolean): (A,B,C,D) = sys.error("Can't execute non-deterministic choose")
  @ignore def choose[A,B,C,D,E](predicate: (A,B,C,D,E) => Boolean): (A,B,C,D,E) = sys.error("Can't execute non-deterministic choose")

  @ignore def decreases(r1: BigInt): Unit = ()
  @ignore def decreases(r1: BigInt, r2: BigInt): Unit = ()
  @ignore def decreases(r1: BigInt, r2: BigInt, r3: BigInt): Unit = ()
  @ignore def decreases(r1: BigInt, r2: BigInt, r3: BigInt, r4: BigInt): Unit = ()
  @ignore def decreases(r1: BigInt, r2: BigInt, r3: BigInt, r4: BigInt, r5: BigInt): Unit = ()

  @ignore def decreases(r1: Int): Unit = ()
  @ignore def decreases(r1: Int, r2: Int): Unit = ()
  @ignore def decreases(r1: Int, r2: Int, r3: Int): Unit = ()
  @ignore def decreases(r1: Int, r2: Int, r3: Int, r4: Int): Unit = ()
  @ignore def decreases(r1: Int, r2: Int, r3: Int, r4: Int, r5: Int): Unit = ()

  @ignore
  implicit class WhileDecorations(u: Unit) {
    def invariant(x: Boolean): Unit = {
      require(x)
      u
    }
  }

  @ignore
  def error[T](reason: java.lang.String): T = sys.error(reason)

  @ignore
  def old[T](value: T): T = value

  @library
  implicit class SpecsDecorations[A](val underlying: A) {
    @ignore
    def computes(target: A) = {
      underlying
    } ensuring {
      res => res == target
    }
  }

  @library
  implicit class StringDecorations(val underlying: String) {
    @ignore @inline
    def bigLength() = BigInt(underlying.length)
    @ignore @inline
    def bigSubstring(start: BigInt): String = underlying.substring(start.toInt)
    @ignore @inline
    def bigSubstring(start: BigInt, end: BigInt): String = underlying.substring(start.toInt, end.toInt)
  }

  @ignore
  object BigInt {
    def apply(b: Int): scala.math.BigInt = scala.math.BigInt(b)
    def apply(b: String): scala.math.BigInt = scala.math.BigInt(b)

    def unapply(b: scala.math.BigInt): scala.Option[Int] = {
      if(b >= Integer.MIN_VALUE && b <= Integer.MAX_VALUE) {
        scala.Some(b.intValue())
      } else {
        scala.None
      }
    }
  }

  @library
  def tupleToString[A, B](t: (A, B), mid: String, f: A => String, g: B => String) = {
    f(t._1) + mid + g(t._2)
  }

  @extern @library
  def print(x: String): Unit = {
    scala.Predef.print(x)
  }

}
