object Requires {

  def f(x: BigInt): Unit = {
    require(0 <= x && x <= 100)
    val y = x + 2
    require(y * y >= x + 40)
  }

  def g: Unit = {
    f(10)
  }

}
