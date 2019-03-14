import stainless.lang._

object OddEvenMoreComplex {

  def isOdd(n: BigInt): Boolean = {
    decreases(if(n < 0) -3*n else 2*n)
    if(n < 0) isOdd(-n)
    else if(n == 0) false
    else isEven(n-1)
  }

  def isEven(n: BigInt): Boolean = {
    decreases(if(n < 0) -4*n else 2*n + 1)
    if(n < 0) isEven(-n)
    else if(n == 0) true
    else !isOdd(n)
  }
}
