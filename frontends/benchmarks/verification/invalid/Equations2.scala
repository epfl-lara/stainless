import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations2 {
  @extern
  def makeEqual(x: BigInt, y: BigInt): Unit = {
    (??? : Unit)
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt) = {
    x ==:| trivial |:
    y ==:| makeEqual(x,y) |:
    x
  }
}
