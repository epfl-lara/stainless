import leon.lang._

object Simple {

  def failling_1(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 0))
    f(-1)
  } ensuring { res => res > 0 }

  def failling_2(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 1))
    f(1) + f(2)
  } ensuring { res => res > 4 }

  def failling_4(f: BigInt => BigInt, g: BigInt => BigInt, x: BigInt) = {
    require(forall((a: BigInt, b: BigInt) => f(a) + g(a) > 0))
    if(x < 0) f(x) + g(x)
    else x
  } ensuring { res => res > 0 }
}
