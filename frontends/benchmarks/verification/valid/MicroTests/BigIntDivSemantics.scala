import stainless.lang._

/** `BigInt` division and remainder round toward zero, as on the JVM, and `mod` is never negative.
  *
  * The divisors are constants, so that the properties stay in linear arithmetic.
  */
object BigIntDivSemantics {
  def basics(): Boolean = {
    BigInt(-7) / 2 == -3 && BigInt(7) / -2 == -3 && BigInt(-7) / -2 == 3 &&
    BigInt(-7) % 2 == -1 && BigInt(7) % -2 == 1 && BigInt(-7) % -2 == -1 &&
    BigInt(-7).mod(2) == 1
  }.ensuring(res => res)

  def divisionIdentity(x: BigInt): Boolean = {
    (x / 3) * 3 + x % 3 == x && (x / -3) * -3 + x % -3 == x
  }.ensuring(res => res)

  def remainderHasTheSignOfTheDividend(x: BigInt): Boolean = {
    val (r1, r2) = (x % 3, x % -3)
    (x >= 0 ==> (r1 >= 0 && r2 >= 0)) && (x <= 0 ==> (r1 <= 0 && r2 <= 0))
  }.ensuring(res => res)

  def divisionIsOdd(x: BigInt): Boolean = {
    -(x / 3) == (-x) / 3 && -(x / 3) == x / -3
  }.ensuring(res => res)

  def modIsNonNegative(x: BigInt): Boolean = {
    val r = x.mod(3)
    0 <= r && r < 3
  }.ensuring(res => res)
}
