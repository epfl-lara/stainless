// Examples are figures from paper:
// Regression Verification for unbalanced recursive functions
// https://iew.technion.ac.il/~ofers/publications/fm16.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Factorial {

  // Fig. 14

  def fact14_1(n: BigInt): BigInt =
    if (n <= 1) 1
    else n * fact14_1(n-1)

  def fact14_2(n: BigInt): BigInt =
    if (n <= 1) 1
    else if (n == 10) 3628800
    else n * fact14_2(n-1)
}