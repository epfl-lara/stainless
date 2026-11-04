import stainless.lang._

object OperandOrder {
  def f: Unit = {
    var x = BigInt(0)

    val r = x + { x += 1; x }

    assert(r == 2)
  }
}
