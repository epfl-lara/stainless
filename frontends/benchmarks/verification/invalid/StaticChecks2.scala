import stainless.lang.StaticChecks._

object StaticChecks2 {

  def foo(n: BigInt, m: BigInt) = {
    assert(n + m > n)
  }

}
