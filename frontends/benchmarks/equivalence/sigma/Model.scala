import stainless.collection._
import stainless.lang._

// This one is expected to timeout, but we want to test that permutation of arguments
// for auxiliary functions does not go wrong when doing a "model first"
// and "candidate first" induction strategy
object Model {

  def sigma(f: BigInt => BigInt, a: BigInt, b: BigInt): BigInt = {
    def s(a: BigInt, b: BigInt, f: BigInt => BigInt, acc: BigInt): BigInt = {
      decreases(if (b == a) BigInt(2) else if (b > a) 2 + b - a else a - b)
      if (a > b) acc else s(a + BigInt(1), b, f, acc + f(a))
    }

    s(a, b, f, BigInt(0))
  }
}
