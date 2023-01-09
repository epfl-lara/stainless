// Examples are figures from paper:
// Automating Regression Verification.
// https://doi.org/10.1145/2642937.2642987

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Limit2 {

  def limit2_1(n: BigInt): BigInt = {
    if (n <= 0) n
    else n + limit2_1(n-1)
  }

  def limit2_2(n: BigInt): BigInt = {
    if (n <= 1) n
    else n + limit2_2(n-1)
  }
}