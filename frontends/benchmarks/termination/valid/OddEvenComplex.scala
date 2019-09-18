/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object OddEvenComplex {

  def rank(n: BigInt): BigInt = {
    if(n < 0) -2*n
    else n
  }

  def isOdd(n: BigInt): Boolean = {
    decreases(rank(n))
    if(n < 0) isOdd(-n)
    else if(n == 0) false
    else isEven(n-1)
  }

  def isEven(n: BigInt): Boolean = {
    decreases(rank(n)) // note: here we need a measure for both functions as they are self-recursive
    if(n < 0) isEven(-n)
    else if(n == 0) true
    else isOdd(n-1)
  }

}
