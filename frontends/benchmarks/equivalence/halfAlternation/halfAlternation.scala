// Examples are figures from paper:
// Regression verification of unbalanced recursive functions with multiple calls (long version)
// https://arxiv.org/pdf/2207.14364.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object HalfAlternation {

  // Fig. 14

  def h1(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n == 1) 1
    else h1(n - 1) + h1 (n - 2)
  }

  def h2(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n == 1) 1
    else if ((n % 2) == 0) h2(n-1) + h2(n-2)
    else h2(n-2) + h2(n-2) + h2(n-3)
  }
}