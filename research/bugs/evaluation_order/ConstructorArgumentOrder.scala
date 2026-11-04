import stainless.lang._

object ConstructorArgumentOrder {
  case class Pair(a: BigInt, b: BigInt)

  def f: Unit = {
    var x = BigInt(0)

    val p = Pair(x, { x += 1; x })

    assert(p.a == 1)
  }
}
