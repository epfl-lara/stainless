// Examples are figures from paper:
// Automating Regression Verification.
// https://doi.org/10.1145/2642937.2642987

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Limit3 {

  def limit3_1(n: BigInt): BigInt = {
    if (n <= 1) n
    else n + limit3_1(n-1)
  }

  def limit3_2(n: BigInt): BigInt = {
    if (n <= 1) n
    else {
      val r = limit3_2(n-1)
      if (r >= 0) n + r
      else r
    }
  }
}