import stainless.collection._
import stainless.lang._


object Candidate {

  def sigma(f: BigInt => BigInt, a: BigInt, b: BigInt): BigInt = {
    decreases(if (b == a) BigInt(2) else if (b > a) 2 + b - a else a - b)

    def sigma_rec(
        sum: BigInt,
        i: BigInt,
        b: BigInt,
        f: BigInt => BigInt
    ): BigInt = {
      decreases(if (b == i) BigInt(2) else if (b > i) 2 + b - i else i - b)
      if (i < b) sigma_rec(sum + f(i), i + BigInt(1), b, f)
      else if (i == b) sum + f(i)
      else BigInt(0)
    }
    if (a > b) BigInt(0) else sigma_rec(BigInt(0), a, b, f)
  }
}
