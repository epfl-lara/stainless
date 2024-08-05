object UNSATPrecond1 {
  def f(x: BigInt): BigInt = {
    require(x > 0)
    require(x < 0)
    x
  }
}
