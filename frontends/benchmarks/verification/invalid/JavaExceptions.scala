// The package keeps the top-level `IllegalArgumentException` of the `Throw` benchmark out of scope, and only
// the decorations are imported, so that the names of exceptions refer to the Java ones
package javaexceptions

import stainless.lang.BooleanDecorations

// The Java exceptions keep the hierarchy of Java: a handler catches no exception of a superclass or of
// a sibling class.
object JavaExceptions {
  def sibling(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new IllegalArgumentException("sibling")
      x
    } catch {
      case _: IllegalStateException => BigInt(1)
    }
  }

  def superclass(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new RuntimeException("superclass")
      x
    } catch {
      case _: IllegalArgumentException => BigInt(1)
    }
  }

  def exception(x: BigInt): BigInt = {
    try {
      if (x == 0) throw new Exception("exception")
      x
    } catch {
      case _: RuntimeException => BigInt(1)
    }
  }

  def exact(): Boolean = {
    (new IllegalStateException("exact"): RuntimeException).isInstanceOf[IllegalArgumentException]
  }.holds
}
