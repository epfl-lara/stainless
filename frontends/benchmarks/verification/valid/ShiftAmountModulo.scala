
// On the JVM, the shift amount of `Int` and `Long` shifts is taken modulo the width
object ShiftAmountModulo {

  def intShifts(x: Int, n: Int): Unit = {
    assert((x << n) == (x << (n & 31)))
    assert((x >> n) == (x >> (n & 31)))
    assert((x >>> n) == (x >>> (n & 31)))
  }

  def longShifts(x: Long, n: Int): Unit = {
    assert((x << n) == (x << (n & 63)))
    assert((x >> n) == (x >> (n & 63)))
    assert((x >>> n) == (x >>> (n & 63)))
  }

  def intExamples(n: Int): Unit = {
    require(n == 33)
    assert((1 << n) == 2)
    assert((1 << (n - 1)) == 1)
    assert((1 << -n) == Int.MinValue)
    assert((Int.MinValue >> n) == Int.MinValue / 2)
    assert((Int.MinValue >>> n) == (1 << 30))
  }

  def longExamples(n: Int): Unit = {
    require(n == 65)
    assert((1L << n) == 2L)
    assert((1L << (n - 1)) == 1L)
    assert((1L << -n) == Long.MinValue)
    assert((Long.MinValue >> n) == Long.MinValue / 2)
    assert((Long.MinValue >>> n) == (1L << 62))
  }

}
