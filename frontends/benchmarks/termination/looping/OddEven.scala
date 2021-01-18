/* Copyright 2009-2021 EPFL, Lausanne */


object OddEven {

  def looping_isOdd(n: BigInt): Boolean = {
    looping_isEven(n-1)
  } ensuring { res => (n % 2 == 1) == res }
  
  def looping_isEven(n: BigInt): Boolean = {
    looping_isOdd(n-1)
  } ensuring { res => (n % 2 == 0) == res }
  
  
}
