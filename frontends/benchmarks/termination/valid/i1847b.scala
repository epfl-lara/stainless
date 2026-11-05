import stainless.lang.*

object i1847b:
  def f(n: BigInt): BigInt =
    require(n >= 0)
    decreases(n)
    if n == 0 then BigInt(0) else g(n - 1, 0)

  def h(a: BigInt, b: BigInt): BigInt =
    require(a >= 0 && b >= 0)
    decreases(a, b)
    if a == 0 then BigInt(0) else g(a - 1, b)

  def g(n: BigInt, m: BigInt): BigInt =
    require(n >= 0 && m >= 0)
    if m == 0 then f(n) else h(n, m - 1)
