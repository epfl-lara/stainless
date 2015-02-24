import leon.annotation._
import leon.lang._

object Rationals { 
  // Represents n/d
  case class Q(n: BigInt, d: BigInt)

  def +(a: Q, b: Q) = {
    require(isRational(a) && isRational(b))

      Q(a.n*b.d + b.n*a.d, a.d*b.d)
  } ensuring {
    isRational(_)
  }

  //def isRational(a: Q) = a.d != 0
  def isRational(a: Q) = a.d != 0

}
