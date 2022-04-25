import stainless.lang._

object NegativeDatatype {
  sealed abstract class Code
  case class Fold(f: Code => Boolean) extends Code

  def looping(c: Code): Boolean = c match {
    case Fold(f) => !f(c)
  }
}
