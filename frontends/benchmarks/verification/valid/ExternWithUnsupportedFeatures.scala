import stainless.annotation._

object ExternWithUnsupportedFeatures {
  @extern
  def f(x: BigInt): Unit = {
    require(x >= 10)
    val t = x.toString // Unsupported construct, but we should still be able to extract f
  }

  def callF: Unit = f(10)
}