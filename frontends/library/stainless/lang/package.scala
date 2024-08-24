/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation._
import stainless.lang.StaticChecks._
import stainless.lang.Cell

package object lang {

  // TODO: should be renamed to ghostExpr
  @library
  def ghost[A](@ghost value: => A): Unit = ()

  @library
  def indexedAt[T](n: BigInt, t: T): T = (??? : T)

  @ignore
  implicit class BooleanDecorations(val underlying: Boolean) {
    def holds : Boolean = {
      underlying
   }.ensuring {
      (res: Boolean) => res
    }

    def holds(becauseOfThat: Boolean) = {
      underlying
   }.ensuring {
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

  @library
  @extern
  def Exception(msg: String): Exception = new Exception{}

  @library
  sealed abstract class Try[T]{
    def map[U](f: T => U): Try[U] = this match {
      case Success(t) => Success(f(t))
      case Failure(exc: Exception) => Failure(exc)
    }

    inline def flatMap[U](f: T => Try[U]): Try[U] = this match {
      case Success(t) => f(t)
      case Failure(exc: Exception) => Failure(exc)
    }
  }
  @library case class Success[T](t: T) extends Try[T]
  @library case class Failure[T](exc: Exception) extends Try[T]

  /* // This would be a widely applicable implicit
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
   */

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

  // TODO: put into a separate library
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

  @ignore @library
    def swap[@mutable T](c1: Cell[T], c2: Cell[T]): Unit = {
      val t = c2.v
      c2.v = c1.v
      c1.v = t
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

  // Forall is opaque forall with (numbers in name instead of overloading)
  @ghost @opaque @library
  def Forall[A](p: A => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall2[A,B](p: (A,B) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall3[A,B,C](p: (A,B,C) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall4[A,B,C,D](p: (A,B,C,D) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall5[A,B,C,D,E](p: (A,B,C,D,E) => Boolean): Boolean = forall(p)

  // We instantiate it explicitly.
  @ghost @opaque @library
  def ForallOf[A](p: A => Boolean)(a: A): Unit = {
    require(Forall(p))
    unfold(Forall(p))
  }.ensuring(_ => p(a))

  // Predicates of larger arity
  @ghost @opaque @library
  def Forall2of[A,B](p: (A,B) => Boolean)(a: A, b: B): Unit = {
    require(Forall2(p))
    unfold(Forall2(p))
  }.ensuring(_ => p(a,b))
  @ghost @opaque @library
  def Forall3of[A,B,C](p: (A,B,C) => Boolean)(a: A, b: B, c: C): Unit = {
    require(Forall3(p))
    unfold(Forall3(p))
  }.ensuring(_ => p(a,b,c))
  @ghost @opaque @library
  def Forall4of[A,B,C,D](p: (A,B,C,D) => Boolean)(a: A, b: B, c: C, d: D): Unit = {
    require(Forall4(p))
    unfold(Forall4(p))
  }.ensuring(_ => p(a,b,c,d))
  @ghost @opaque @library
  def Forall5of[A,B,C,D,E](p: (A,B,C,D,E) => Boolean)(a: A, b: B, c: C, d: D, e: E): Unit = {
    require(Forall5(p))
    unfold(Forall5(p))
  }.ensuring(_ => p(a,b,c,d,e))

}
