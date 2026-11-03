
object MultiplyMinValueByMinusOne {

  // -1 * MinValue overflows (the product is 2^31, resp. 2^63). It was accepted by the former overflow check
  // `rhs == (lhs * rhs) / lhs`, because MinValue / -1 wraps around to MinValue in bitvector arithmetic.
  def int(x: Int): Int = {
    require(x == Int.MinValue)
    -1 * x
  }

  def long(x: Long): Long = {
    require(x == Long.MinValue)
    -1L * x
  }

}
