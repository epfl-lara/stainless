import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations {
  @library
  def makeEqual(x: BigInt, y: BigInt) = {
    true
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt, z: BigInt, t: BigInt) = {
    x ==:| makeEqual(x,y) |:
    y ==:| makeEqual(y,z) |:
    z ==:| makeEqual(z,t) |:
    t
  }
}
