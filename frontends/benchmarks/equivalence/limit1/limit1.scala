// Examples are figures from paper:
// Automating Regression Verification.
// https://doi.org/10.1145/2642937.2642987

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Limit1 {

  // REVE does not work -- requires manual unrolling

  def limit1_1(n: BigInt): BigInt = {
    if (n <= 1) n
    else n + limit1_1(n-1)
  }

  def limit1_2(n: BigInt): BigInt = {
    if (n <= 1) n
    else n + n-1 + limit1_2(n-2)
  }
}