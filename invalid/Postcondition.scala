import leon.lang._

object Postconditions {
  def failling_1(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 0))
    f(10)
  } ensuring { res => forall((a: BigInt) => res > f(a)) }

  def failling_2(f: BigInt => BigInt, x: BigInt) = {
    require(x >= 0 && forall((a: BigInt) => a > 0 ==> f(a) < 0))
    x
  } ensuring { res => forall((a: BigInt) => res > f(a)) }

}
