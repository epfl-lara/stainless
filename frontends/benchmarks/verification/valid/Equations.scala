import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations {
  @extern
  def makeEqual(x: BigInt, y: BigInt): Unit = {
    (??? : Unit)
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt, z: BigInt, t: BigInt) = {
    x ==:| makeEqual(x,y) |:
    y ==:| makeEqual(y,z) |:
    z ==:| makeEqual(z,t) |:
    t
  }
}
