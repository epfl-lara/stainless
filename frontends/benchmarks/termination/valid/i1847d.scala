import stainless.lang.*

object i1847d:
  def f(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n < 2 then BigInt(1) else g(n)

  def g(n: BigInt): BigInt =
    require(n >= 2)
    val a: BigInt = f(n - 1)
    val b: BigInt = f(n - 2)
    a + b
