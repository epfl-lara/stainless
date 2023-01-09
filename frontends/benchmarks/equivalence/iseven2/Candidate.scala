import stainless.lang._
import stainless.collection._

object Candidate {

  def isEvenTopLvl(x: BigInt): Boolean = !myIsOdd(x) && myIsEven(x) // Note: swapped order to cause "pairs" to be mismatched

  def myIsOdd(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x <= 0) false
    else if (x == 1) true
    else !myIsEven(x - 1)
  }
  def myIsEven(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x < 0) false
    else if (x == 0) true
    else myIsEven(x - 2)
  }
}