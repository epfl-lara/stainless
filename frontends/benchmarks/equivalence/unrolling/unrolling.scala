// Examples are figures from paper:
// Regression Verification for unbalanced recursive functions
// https://iew.technion.ac.il/~ofers/publications/fm16.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Unrolling {

  // Fig. 13

  def fact13_1(n: BigInt): BigInt =
    if (n <= 1) 1
    else if (n == 2) 2
    else if (n == 3) 6
    else if (n == 4) 24
    else n * (n-1) * (n-2) * (n-3) * fact13_1(n-4)

  def fact13_2(n: BigInt): BigInt =
    if (n <= 1) 1
    else if (n == 2) 2
    else if (n == 3) 6
    else if (n == 4) 24
    else if (n == 5) 120
    else if (n == 6) 720
    else if (n == 7) 5040
    else if (n == 8) 40320
    else n * (n-1) * (n-2) * (n-3) * fact13_2(n-4)

}