import leon.lang._
import leon.collection._
import leon._

object BVDivisionByZero {

  def noDivByZero(x: Int): Boolean = {
    (x / 10 == 10)
  }

  def noRemByZero(x: BigInt): Boolean = {
    (x % 10 == 10)
  }
  
}
