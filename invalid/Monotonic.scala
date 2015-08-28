import leon.lang._

object Monotonic {
  def failling_1(f: BigInt => BigInt, g: BigInt => BigInt): BigInt => BigInt = {
    require(forall((a: BigInt, b: BigInt) => (a > b ==> f(a) > f(b))))
    (x: BigInt) => f(g(x))
  } ensuring { res => forall((a: BigInt, b: BigInt) => a > b ==> res(a) > res(b)) }
}

// vim: set ts=4 sw=4 et:
