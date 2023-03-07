// Examples are figures from paper:
// Regression Verification for unbalanced recursive functions
// https://iew.technion.ac.il/~ofers/publications/fm16.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Sum {

  // Fig. 5 - two functions are not in lock-step

  def sum1(n: BigInt): BigInt =
    if (n <= 1) n
    else n + n-1 + sum1(n-2)

  def sum2(n: BigInt): BigInt =
    if (n <= 1) n
    else n + sum2(n-1)
}