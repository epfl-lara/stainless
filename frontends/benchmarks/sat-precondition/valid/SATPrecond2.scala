object SATPrecond2 {
  def f(x: BigInt, y: BigInt): BigInt = {
    require(x > 0)
    require(y > 0)
    require(x < y)
    x + y
  }
}
