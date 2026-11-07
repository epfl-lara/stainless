import stainless.lang.*

object i1847f:
  def a(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n == 0 then BigInt(0) else b(n - 1)

  def b(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n == 0 then BigInt(0) else a(n - 1)

  def f(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n == 0 then BigInt(0) else g(n - 1)

  def g(n: BigInt): BigInt =
    require(n >= 0)
    a(n + 1) + f(n)
