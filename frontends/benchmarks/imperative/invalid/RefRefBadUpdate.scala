import stainless.lang._

object RefRefBadUpdate {
  case class Box(var value: BigInt)
  case class RefRef(var lhs: Box, var rhs: Box)

  def replaceLhs(rr: RefRef, v: BigInt): Unit = {
    rr.lhs = Box(v)
  }

  def f(rr: RefRef): Unit = {
    val lhs = rr.lhs
    val old = lhs.value

    replaceLhs(rr, 123)

    assert(lhs.value == old)
    assert(rr.lhs.value == 123)

    rr.lhs.value = 456

    assert(lhs.value == 456)
    assert(rr.lhs.value == 456)
  }
}
