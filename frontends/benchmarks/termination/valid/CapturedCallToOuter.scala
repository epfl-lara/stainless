import stainless.lang._

// Inner functions capture a binding whose definition calls the outer function. Lifting an inner
// function must not copy that call into it, which would make it mutually recursive with the outer
// function, whose calls the type checker then rejects.
object CapturedCallToOuter {
  def withMeasures(n: BigInt): BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) BigInt(0)
    else {
      val b = withMeasures(n - 1)
      def count(i: BigInt): BigInt = {
        require(i >= 0)
        decreases(i)
        if (i == 0) b else count(i - 1) + 1
      }
      count(n)
    }
  }

  def inferred(n: BigInt): BigInt = {
    if (n <= 0) BigInt(0)
    else {
      val b = inferred(n - 1)
      def count(i: BigInt): BigInt = {
        if (i <= 0) b else count(i - 1) + 1
      }
      count(n)
    }
  }

  // The capture holds a function, which `--function-equality=none` can't compare
  def withFunction(n: BigInt): BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) BigInt(0)
    else {
      val prev = withFunction(n - 1)
      val f = (x: BigInt) => x + prev
      def count(i: BigInt): BigInt = {
        require(i >= 0)
        decreases(i)
        if (i == 0) f(0) else count(i - 1) + 1
      }
      count(n)
    }
  }
}
