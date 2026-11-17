import stainless.lang.*

object IntToBigInt:
  def f(i: BigInt): BigInt = i

  def g(i: Int): BigInt = {
    f(i)
  }.ensuring(res => res == BigInt(i))

  def implicitInt(x: Int): Boolean = {
    val b: BigInt = x
    b == BigInt(x)
  }.holds

  def implicitLong(x: Long): Boolean = {
    val b: BigInt = x
    b == BigInt(x)
  }.holds

  def implicitInArithmetic(b: BigInt, x: Int): Boolean = {
    b + x == b + BigInt(x)
  }.holds

  def implicitInComparison(b: BigInt, x: Int): Boolean = {
    (b < x) == (b < BigInt(x))
  }.holds

  def implicitInPostcondition(x: Int): Unit = {
    ()
  }.ensuring(_ => f(x) == BigInt(x))

  // The type of an `if` or a `match` of literals is a union of literal types, such as `(1 : Int) | (0 : Int)`
  def ifArgument(c: Boolean): Boolean = {
    BigInt(if c then 1 else 0) == (if c then BigInt(1) else BigInt(0))
  }.holds

  def longIfArgument(c: Boolean): Boolean = {
    BigInt(if c then 1L else 0L) >= 0
  }.holds

  def matchArgument(x: Int): Boolean = {
    BigInt(
      x match
        case 0 => 1
        case _ => 2
    ) > 0
  }.holds
