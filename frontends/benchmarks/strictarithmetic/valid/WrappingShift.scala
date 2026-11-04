import stainless.annotation._

object WrappingShift {

  // In wrapping mode, shift amounts are not checked to be non-negative
  @wrapping
  def negativeAmounts(n: Int): Unit = {
    require(n == -1)
    assert((1 << n) == Int.MinValue)
    assert((1L << n) == Long.MinValue)
  }

}
