import stainless.lang.*

/** Failing assertions whose message must appear in the kind of their VC. */
object AssertMessages:

  /** A call to `assert`, which Scala 3 inlines during typer. */
  def plainAssert(x: BigInt): BigInt =
    assert(x > 0, "x is positive")
    x

  /** An inline method: Scala 3 does not expand the `assert` in its body. */
  inline def inlineAssert(x: BigInt): Unit =
    assert(x > 1, "x is greater than one")

  /** A call to an inline method that calls `assert`. */
  def callsInlineAssert(x: BigInt): BigInt =
    inlineAssert(x)
    x
