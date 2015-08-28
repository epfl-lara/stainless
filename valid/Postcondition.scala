import leon.lang._

object Postconditions {

  def passing_1(f: BigInt => BigInt, x: BigInt) = {
    require(x >= 0 && forall((a: BigInt) => f(a) < 0))
    x
  } ensuring { res => forall((a: BigInt) => res > f(a)) }

  def passing_2(f: BigInt => BigInt, x: BigInt) = {
    require(x >= 0 && forall((a: BigInt) => a > 0 ==> f(a) < 0))
    x
  } ensuring { res => forall((a: BigInt) => a > 0 ==> res > f(a)) }

  def passing_3(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => f(a) > 0))
    f
  } ensuring { res => forall((a: BigInt) => res(a) > 0) }

  def passing_4() = {
    (x: BigInt) => x + 1
  } ensuring { res => forall((a: BigInt) => res(a) > a) }
}
