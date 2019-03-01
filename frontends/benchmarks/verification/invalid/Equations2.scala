import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations2 {
  @library
  def makeEqual(x: BigInt, y: BigInt) = {
    true
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt) = {
    x ==:| trivial |:
    y ==:| makeEqual(x,y) |:
    x
  }
}
