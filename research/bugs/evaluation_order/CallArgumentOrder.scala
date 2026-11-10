import stainless.lang._

object CallArgumentOrder {
  def callee(x1: BigInt, x2: BigInt, x3: BigInt): Unit = {
    require(x1 == 1)
    require(x2 == 3)
    require(x3 == 3)
  }

  def f: Unit = {
    var x = BigInt(0)

    callee({ x += 1; x }, x, { x += 2; x })
  }
}
