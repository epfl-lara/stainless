import stainless.lang._
import stainless.collection._

object Model {

  def isEvenTopLvl(x: BigInt): Boolean = isEven(x)

  def isOdd(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x <= 0) false
    else if (x == 1) true
    else !isEven(x - 1)
  }
  def isEven(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x < 0) false
    else if (x == 0) true
    else !isOdd(x - 1)
  }
}