import stainless.annotation._

object i1274b {
  @extern
  def f(x: BigInt, y: BigInt): Unit = {
    require(x >= 10)
    val t = x.toString // Unsupported construct
    // This extern function contract still misses the following require
    // but we can't resume the extraction after having encountered an
    // unsupported feature. We must reject to program because this require
    // will be erased, akin to SneakySpecsInExtern1.
    require(x >= y)
  }

  def callF: Unit = f(10, 10)
}