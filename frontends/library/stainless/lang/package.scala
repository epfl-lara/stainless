/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import stainless.annotation._
import scala.language.implicitConversions

package object lang {
  import stainless.proof._

  @library
  implicit class BooleanDecorations(val underlying: Boolean) {
    @inline
    def holds : Boolean = {
      underlying
    } ensuring {
      (res: Boolean) => res
    }
    @inline
    def holds(becauseOfThat: Boolean) = {
      underlying
    } ensuring {
      (res: Boolean) => becauseOfThat && res
    }

    @inline
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

  @library
  implicit class FunctionSpecs1[A,R](val f: A => R) {
    @ignore def pre: A => Boolean = sys.error("Can't execute first-class contract")
    def requires(p: A => Boolean): Boolean = forall((a: A) => p(a) ==> f.pre(a))
    def ensures(p: (A,R) => Boolean): Boolean = forall((a: A) => f.pre(a) ==> p(a,f(a)))
  }

  @library
  implicit class FunctionSpecs2[A,B,R](val f: (A,B) => R) {
    @ignore def pre: (A,B) => Boolean = sys.error("Can't execute first-class contract")
    def requires(p: (A,B) => Boolean): Boolean = forall((a: A, b: B) => p(a,b) ==> f.pre(a,b))
    def ensures(p: (A,B,R) => Boolean): Boolean = forall((a: A, b: B) => f.pre(a,b) ==> p(a,b,f(a,b)))
  }

  @library
  implicit class FunctionSpecs3[A,B,C,R](val f: (A,B,C) => R) {
    @ignore def pre: (A,B,C) => Boolean = sys.error("Can't execute first-class contract")
    def requires(p: (A,B,C) => Boolean): Boolean =
      forall((a: A, b: B, c: C) => p(a,b,c) ==> f.pre(a,b,c))
    def ensures(p: (A,B,C,R) => Boolean): Boolean =
      forall((a: A, b: B, c: C) => f.pre(a,b,c) ==> p(a,b,c,f(a,b,c)))
  }

  @library
  implicit class FunctionSpecs4[A,B,C,D,R](val f: (A,B,C,D) => R) {
    @ignore def pre: (A,B,C,D) => Boolean = sys.error("Can't execute first-class contract")
    def requires(p: (A,B,C,D) => Boolean): Boolean =
      forall((a: A, b: B, c: C, d: D) => p(a,b,c,d) ==> f.pre(a,b,c,d))
    def ensures(p: (A,B,C,D,R) => Boolean): Boolean =
      forall((a: A, b: B, c: C, d: D) => f.pre(a,b,c,d) ==> p(a,b,c,d,f(a,b,c,d)))
  }

  @ignore def decreases(rank: BigInt): Unit = ()
  @ignore def decreases(rank: (BigInt, BigInt)): Unit = ()
  @ignore def decreases(rank: (BigInt, BigInt, BigInt)): Unit = ()
  @ignore def decreases(rank: (BigInt, BigInt, BigInt, BigInt)): Unit = ()
  @ignore def decreases(rank: (BigInt, BigInt, BigInt, BigInt, BigInt)): Unit = ()

  @ignore def decreases(rank: Int): Unit = ()
  @ignore def decreases(rank: (Int, Int)): Unit = ()
  @ignore def decreases(rank: (Int, Int, Int)): Unit = ()
  @ignore def decreases(rank: (Int, Int, Int, Int)): Unit = ()
  @ignore def decreases(rank: (Int, Int, Int, Int, Int)): Unit = ()

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

  @ignore
  implicit class Passes[A,B](io : (A,B)) {
    val (in, out) = io
    def passes(tests : A => B ) : Boolean =
      try { tests(in) == out } catch { case _ : MatchError => true }
  }
  
  @ignore
  def byExample[A, B](in: A, out: B): Boolean = {
    sys.error("Can't execute by example proposition")
  }
  
  implicit class SpecsDecorations[A](val underlying: A) {
    @ignore
    def computes(target: A) = {
      underlying
    } ensuring {
      res => res == target
    }
    
    @ignore // Programming by example: ???[String] ask input
    def ask[I](input : I) = {
      underlying
    } ensuring {
      (res: A) => byExample(input, res)
    }
  }
  
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
