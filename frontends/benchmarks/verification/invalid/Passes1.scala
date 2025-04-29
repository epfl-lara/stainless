import stainless.lang._

object Passes1 {

  def abs(n: BigInt): BigInt = {
    if (n < 0) -n else n
  }.ensuring { res =>
    res >= 0 &&
      ((n, res) passes {
        case BigInt(-42) => BigInt(0)
      })
  }

}
