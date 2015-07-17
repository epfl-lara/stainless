import leon.lang._
import leon.collection._
import leon._

object RealDivisionByZero {

  def divByZero(x: Real): Boolean = {
    (x / Real(0) == Real(10))
  }

}
