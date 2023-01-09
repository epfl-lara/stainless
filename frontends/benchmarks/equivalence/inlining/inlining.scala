// Examples are figures from paper:
// Automating Regression Verification.
// https://doi.org/10.1145/2642937.2642987

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Inlining {

  def inlining_1(x: BigInt): BigInt = {
    if (x > 0) inlining_1(x-1) + BigInt(1)
    else if (x < 0) 0
    else x
  }

  def inlining_2(x: BigInt): BigInt = {
    if (x > 1) inlining_2(x-2) + BigInt(2)
    else if (x < 0) 0
    else x
  }
}