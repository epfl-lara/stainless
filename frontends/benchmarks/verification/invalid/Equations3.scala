import stainless.equations._
import stainless.annotation._
import stainless.lang._

object Equations3 {
  @extern
  def makeEqual(x: BigInt, y: BigInt): Unit = {
    (??? : Unit)
  } ensuring(_ => x == y)

  def f(x: BigInt, y: BigInt, z: BigInt) = {
    (
      x ==:| makeEqual(x,y) |:
      y ==:| makeEqual(y,z) |:
      z
    ).qed

    assert(x == z) // OK
    assert(z == y) // Not OK, as we don't want the internals of equations to leak outside
  }
}
