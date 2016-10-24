import leon.lang.StaticChecks._

object StaticChecks2 {

  def add(n: BigInt, m: BigInt): BigInt = {
    require(n >= 0 && m >= 0)
    var res = if(m == 0) n else add(n, m-1) + 1
    assert(res >= 0)
    res
  } ensuring((res: BigInt) => res >= 0)


}
