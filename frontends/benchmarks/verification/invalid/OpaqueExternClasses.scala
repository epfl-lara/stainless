import stainless.lang._
import stainless.annotation._

object OpaqueExternClasses {
  @extern
  class Counter(val underlying: java.util.concurrent.atomic.AtomicLong) {
    def next(): BigInt = {
      BigInt(underlying.incrementAndGet())
    }.ensuring(res => res > 0)

    @pure
    def current: BigInt = BigInt(underlying.get())
  }

  // `next` may modify the counter, so its current value may change
  def unchanged(c: Counter): Unit = {
    val before = c.current
    c.next()
    assert(c.current == before)
  }
}
