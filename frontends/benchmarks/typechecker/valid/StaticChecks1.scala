import stainless.lang._
import stainless.lang.StaticChecks._

object StaticChecks1 {

  def add(n: BigInt, m: BigInt): BigInt = {
    require(n >= 0 && m >= 0)
    decreases(m)
    if(m == 0) n else add(n, m-1) + 1
  } ensuring((res: BigInt) => res >= 0)

}
