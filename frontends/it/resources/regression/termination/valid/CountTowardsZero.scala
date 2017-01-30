/* Copyright 2009-2016 EPFL, Lausanne */


object Test {
  def f(x: BigInt): BigInt = {
    if (x == 0) {
      BigInt(0)
    } else if (x > 0) {
      f(x-1)+2
    } else if (x < 0) {
      f(x+1)-2
    } else {
      BigInt(33)
    }
  } ensuring (_ == x*2)
}
