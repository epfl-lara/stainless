import stainless.lang._
import stainless.annotation._

object Power {

  def power(x: BigInt, y: BigInt) : BigInt = {
    require(y >= 0 && x >= 1)
    if(y < 1) BigInt(1)
    else
      x * power(x, y - 1)
  }ensuring(_ >= 1)
  
  @traceInduct("")
  def powerMonotone(x1: BigInt, x2: BigInt, y: BigInt) = {
    require(y >= 0)
    (1 <= x1 && x1 <= x2) ==> power(x1, y) <= power(x2, y)
  }.holds
}

