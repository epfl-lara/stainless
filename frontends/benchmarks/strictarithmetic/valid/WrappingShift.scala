import stainless.annotation._
import stainless.math.wrapping

// In wrapping mode, the amount of `Int` and `Long` shifts is not checked: it is
// taken modulo the width, as on the JVM
object WrappingShift {

  @wrapping
  def negativeAmounts(n: Int): Unit = {
    require(n == -1)
    assert((1 << n) == Int.MinValue)
    assert((1L << n) == Long.MinValue)
  }

  @wrapping
  def amountsBeyondTheWidth(n: Int, m: Int): Unit = {
    require(n == 33 && m == 65)
    assert((1 << n) == 2)
    assert((Int.MinValue >> n) == Int.MinValue / 2)
    assert((Int.MinValue >>> n) == (1 << 30))
    assert((1L << m) == 2L)
    assert((Long.MinValue >> m) == Long.MinValue / 2)
  }

  def wrappingBlocks(x: Int, y: Long, n: Int): Unit = {
    assert(wrapping(x << n) == (x << (n & 31)))
    assert(wrapping(y >>> n) == (y >>> (n & 63)))
  }

}
