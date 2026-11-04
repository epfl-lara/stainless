import stainless.lang._

object TupleArgumentOrder {
  def f: Unit = {
    var x = BigInt(0)

    val p = (x, { x += 1; x })

    assert(p._1 == 1)
  }
}
