import stainless.annotation._

object GoodInitialization {
  case class A(x: BigInt) {
    val y = x
    val z = y + y
  }
  def f(z: BigInt) = {
    assert(A(21).z == 42)
  }
}
