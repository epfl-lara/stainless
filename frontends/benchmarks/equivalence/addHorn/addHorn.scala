// Examples are figures from paper:
// Automating Regression Verification.
// https://doi.org/10.1145/2642937.2642987

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object AddHorn {

  def add_horn_1(i: BigInt, j: BigInt): BigInt = {
    require(i >= 0)
    if (i == 0) j
    else add_horn_1(i-1, j+1)
  }

  def add_horn_2(i: BigInt, j: BigInt): BigInt = {
    require(i >= 0)
    if (i == 0) j
    else if (i == 1) j + 1
    else add_horn_2(i-1, j+1)
  }
}