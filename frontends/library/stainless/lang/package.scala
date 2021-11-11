/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation._
import stainless.lang.StaticChecks._

package object lang {

  @library
  def ghost[A](@ghost value: A): Unit = ()

  @library
  def indexedAt[T](n: BigInt, t: T): T = (??? : T)

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

    // Use this "and" operator instead of `&&` when you want verification conditions to be split
    def &&&(that: => Boolean): Boolean = {
      if (underlying) that else false
    }
  }

  @library
  abstract class Exception extends Throwable

  @ignore
  implicit class Throwing[T](underlying: => T) {
    def throwing(pred: Exception => Boolean): T = try {
      underlying
    } catch {
      case e: Exception =>
        assert(pred(e))
        throw e
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

  @ignore def decreases(@ghost r1: Any): Unit = ()
  @ignore def decreases(@ghost r1: Any, @ghost r2: Any): Unit = ()
  @ignore def decreases(@ghost r1: Any, @ghost r2: Any, @ghost r3: Any): Unit = ()
  @ignore def decreases(@ghost r1: Any, @ghost r2: Any, @ghost r3: Any, @ghost r4: Any): Unit = ()
  @ignore def decreases(@ghost r1: Any, @ghost r2: Any, @ghost r3: Any, @ghost r4: Any, @ghost r5: Any): Unit = ()

  @ignore
  implicit class WhileDecorations(val u: Unit) {
    def invariant(x: Boolean): Unit = {
      require(x)
      u
    }

    def noReturnInvariant(x: Boolean): Unit = {
      require(x)
      u
    }

    def inline: Unit = { }
    def opaque: Unit = { }
  }

  @ignore
  def error[T](reason: java.lang.String): T = sys.error(reason)

  @ignore
  def old[T](value: T): T = value

  @ignore @ghost
  def snapshot[T](value: T): T = value

  /** @note for internal and testing use only */
  @ignore
  def freshCopy[T](value: T): T = (??? : T)

  @library
  @partialEval
  def partialEval[A](x: A): A = x

  @library
  implicit class SpecsDecorations[A](val underlying: A) {
    @ignore
    def computes(target: A) = {
      underlying
    } ensuring {
      res => res == target
    }
  }

  @ignore
  implicit class Passes[A, B](io: (A, B)) {
    val (in, out) = io

    @ignore
    def passes(tests: A => B): Boolean = try {
      tests(in) == out
    } catch {
      case _ : MatchError => true
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
        scala.Some(b.intValue)
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

  @library
  def specialize[T](call: T): T = call

  @library
  def inline[T](call: T): T = call

  // typically used when `call` invokes an `opaque` function
  // this adds an equality between the call, and the inlined call
  @library
  def unfold[T](call: T): Unit = ()

  @ignore @library
  implicit class ArrayUpdating[T](a: Array[T]) {
    def updated(index: Int, value: T): Array[T] = {
      val res = a.clone
      res(index) = value
      res
    }
  }

  @ignore @library
  def swap[@mutable T](a1: Array[T], i1: Int, a2: Array[T], i2: Int): Unit = {
    require(
      0 <= i1 && i1 < a1.length &&
      0 <= i2 && i2 < a2.length
    )
    val t = a1(i1)
    a1(i1) = a2(i2)
    a2(i2) = t
  }

  @extern @library @mutable @anyHeapRef
  trait AnyHeapRef {
    @refEq
    def refEq(that: AnyHeapRef): Boolean = true
  }

  @library
  implicit class HeapRefSetDecorations[T <: AnyHeapRef](val objs: Set[T]) {
    @extern @library
    def asRefs: Set[AnyHeapRef] = ???
  }

  @ignore
  def reads(@ghost objs: Set[AnyHeapRef]): Unit = ()

  @ignore
  def modifies(@ghost objs: Set[AnyHeapRef]): Unit = ()

  @extern @library
  def objectId[T <: AnyHeapRef](x: T): BigInt = ???

  @library
  case class Heap(/*opaque*/) {
    // Evaluates a value expression in the given heap.
    // Caveat: Reads and modifies clauses are currently unchecked in the value expression.
    @extern @library
    def eval[T](value: T): T = ???
  }

  object Heap {
    // Returns a snapshot of the current heap.
    @extern @library
    def get: Heap = ???

    // Returns whether two heaps are equal on all the given objects.
    @extern @library
    def unchanged(objs: Set[AnyHeapRef], h0: Heap, h1: Heap): Boolean =
      /* objs.mapMerge(h1, h0) == h0 */ ???
  }
}
