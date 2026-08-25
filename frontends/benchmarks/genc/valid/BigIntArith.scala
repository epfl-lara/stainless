import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.io._

object BigIntArith {

  def compute(a: BigInt, b: BigInt): BigInt = {
    require(0 <= a && a <= 1000000 && 0 <= b && b <= 1000000)
    // On non-negative values, mod coincides with % and both are supported.
    (a + b) * 3 + a / 2 + b % 1000 + (b mod 7)
  }.ensuring(res => 0 <= res && res <= 7000000)

  def diff(a: BigInt, b: BigInt): BigInt = {
    require(0 <= b && b <= a && a <= 1000000)
    a - b // needs b <= a: uint32 subtraction must not go below zero
  }.ensuring(res => 0 <= res && res <= 1000000)

  def sumTo(n: BigInt): BigInt = {
    require(0 <= n && n <= 1000)
    decreases(n)
    if (n <= 0) BigInt(0)
    else n + sumTo(n - 1)
  }.ensuring(res => 0 <= res && res <= 1000 * n)

  // BigInt parameters and results of exported functions become uint32_t in C.
  // Note that preconditions of exported functions may only use comparisons on BigInt
  // (no arithmetic), as they are compiled to runtime checks on unverified C inputs.
  @cCode.`export`
  def scaleClamped(x: BigInt): BigInt = {
    require(0 <= x && x <= 1000000)
    x * 3
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state: State = newState
    StdOut.print(compute(BigInt(1000), BigInt(500)).toInt)
    StdOut.print(diff(BigInt(1000), BigInt(400)).toInt)
    StdOut.println(sumTo(BigInt(100)).toInt)
  }

}
