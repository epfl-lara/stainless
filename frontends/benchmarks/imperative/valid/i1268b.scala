import stainless.lang._

object i1268b {
  case class Box(var value: BigInt) {
    def increment: Box = {
      value += 1
      this
    }
  }

  def outer(b1: Box): Unit = {
    val oldb1 = b1.value
    val b2 = freshCopy(b1).increment
    assert(b1.value == oldb1)
    assert(b2.value == b1.value + 1)

    def inner: Unit = {
      assert(b1.value == oldb1)
      assert(b2.value == b1.value + 1)
    }
  }
}