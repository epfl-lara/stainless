// The package keeps the top-level `IllegalArgumentException` of the `Throw` benchmark out of scope, and only
// the decorations are imported, so that the names of exceptions refer to the Java ones
package javaexceptions

import stainless.lang.{BooleanDecorations, Throwing}

// Java exceptions can be thrown, caught and extended. Stainless extracts them as the classes of the
// same name in `stainless.lang`, which follow the hierarchy of Java.
object JavaExceptions {
  case class FatalError(msg: String) extends Exception(msg)
  class Unsupported extends UnsupportedOperationException("unsupported")

  def check(x: BigInt): BigInt = {
    if (x < 0) throw FatalError("negative")
    if (x > 10) throw new IllegalArgumentException("too large")
    x
  }.ensuring(res => 0 <= res && res <= 10).throwing {
    case FatalError(_) => x < 0
    case _: IllegalArgumentException => x > 10
    case _ => false
  }

  // `RuntimeException` catches its Java subclasses
  def clamp(x: BigInt): BigInt = {
    try check(x) catch {
      case FatalError(_) => BigInt(0)
      case _: RuntimeException => BigInt(10)
    }
  }.ensuring(res => 0 <= res && res <= 10)

  // `Exception` and `Throwable` catch every exception
  def catchAll(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new Unsupported
      if (x == 1) throw new java.util.NoSuchElementException()
      x
    } catch {
      case _: IllegalStateException => BigInt(-1)
      case _: Exception => BigInt(-2)
    }
  }.ensuring(res => (x == 0 || x == 1) ==> (res == -2))

  def catchThrowable(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new ArithmeticException()
      x
    } catch {
      case _: Throwable => BigInt(1)
    }
  }.ensuring(res => x == 0 ==> (res == 1))

  // `new X(...)` builds an `X` and none of its subclasses
  def build(): RuntimeException = new IllegalStateException("build")

  def isExact(): Boolean = {
    val e = build()
    e.isInstanceOf[IllegalStateException] && !e.isInstanceOf[IllegalArgumentException]
  }.holds

  // The Java exceptions are the ones of `stainless.lang`
  def mixed(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new IllegalArgumentException("mixed")
      x
    } catch {
      case _: stainless.lang.RuntimeException => BigInt(1)
    }
  }.ensuring(res => x == 0 ==> (res == 1))

  // A concrete exception class with subclasses, as in Inox
  class SolverError(msg: String) extends Exception(msg)
  case class Timeout(limit: BigInt) extends SolverError("timeout")

  def solve(x: BigInt): BigInt = {
    if (x < 0) throw new SolverError("negative")
    if (x > 100) throw Timeout(100)
    x
  }.throwing {
    case Timeout(limit) => limit == 100 && x > 100
    case _: SolverError => x < 0
    case _ => false
  }

  def solveOr(x: BigInt): BigInt = {
    try solve(x) catch {
      case Timeout(_) => BigInt(100)
      case _: SolverError => BigInt(0)
    }
  }.ensuring(res => 0 <= res && res <= 100)
}
