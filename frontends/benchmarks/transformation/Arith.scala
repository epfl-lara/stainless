/* Copyright 2009-2016 EPFL, Lausanne */


object Arithmetic {

  def test(a: BigInt, b: BigInt, c: BigInt): BigInt = {
    require(a > b && c > BigInt(0))
    c + a
  } ensuring( _ > c + b )

}
