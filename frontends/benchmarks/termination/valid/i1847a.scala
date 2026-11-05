import stainless.lang.*

object i1847a:
  def f(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n <= 0 then BigInt(0) else g(n - 1)

  def g(n: BigInt): BigInt =
    if n <= 1 then BigInt(0)
    else if n % 2 == 0 then f(n - 1)
    else f(n - 2)
