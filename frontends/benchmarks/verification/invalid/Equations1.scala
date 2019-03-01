import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations1 {
  @library
  def makeEqual(x: BigInt, y: BigInt) = {
    true
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt) = {
    x ==:| makeEqual(x,y) |:
    y ==:| trivial |:
    x
  }
}
