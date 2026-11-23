import stainless.lang._
import stainless.annotation._

object ExternPostconditionUnsatisfiable {
  // No result satisfies the postcondition of `pick` when `x` is positive, so callers could prove
  // anything about `pick(x)`.
  @extern
  def pick(x: BigInt): BigInt = {
    require(x > 0)
    (??? : BigInt)
  }.ensuring(res => res > x && res < 0)

  @extern
  def mutate(a: Array[Int]): Unit = {
    require(a.length > 0)
    (??? : Unit)
  }.ensuring(_ => a(0) == 1 && a(0) == 2)

  // A precondition that excludes every argument for which the postcondition can be met
  @extern
  def unreachable(x: BigInt): BigInt = {
    require(x > 10)
    (??? : BigInt)
  }.ensuring(res => res == x && res < 10)
}
