import stainless.lang.*

object i1847c:
  def f(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    g1(n)

  def g1(n: BigInt): BigInt =
    require(n >= 0)
    g2(n) + (if n > 0 then h(n - 1) else BigInt(0))

  def g2(n: BigInt): BigInt =
    require(n >= 0)
    g3(n)

  def g3(n: BigInt): BigInt =
    require(n >= 0)
    if n == 0 then BigInt(0) else f(n - 1)

  def h(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n == 0 then BigInt(0) else g3(n - 1)
