package boxMutation2
import stainless.lang._

object A:
  case class Box(var x: BigInt):
    def getX(): BigInt = x

    def fooRefinement(): {r : Boolean with r == (getX() > 0)} =
      x += 1
      x > 0

    def fooEnsuring(): Boolean = {
      x += 1
      x > 0
    }.ensuring(_ == getX() > 0)
