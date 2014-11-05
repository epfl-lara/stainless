/* Copyright 2009-2014 EPFL, Lausanne */

object AddingPositiveNumbers {

  //this should not overflow
  def additionSound(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0 && y >= 0)
    x + y
  } ensuring(_ >= 0)

}
