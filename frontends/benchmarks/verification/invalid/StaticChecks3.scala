import stainless.lang.StaticChecks._

object StaticChecks3 {

  def add(n: BigInt, m: BigInt): BigInt = {
    require(n >= 0)
    n + m
  }.ensuring { _ >= 0 }

}
