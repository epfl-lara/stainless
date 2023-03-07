// Examples are figures from paper:
// Regression verification of unbalanced recursive functions with multiple calls (long version)
// https://arxiv.org/pdf/2207.14364.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object FullAlternation {

  // Fig. 12

  def m1(n: BigInt, flag: Boolean): BigInt = {
    if (n < 1) 0
    else if (n == 1) 1
    else m1(n - 1, !flag) + m1(n - 2, !flag)
  }

  def m2(n: BigInt, mode: Boolean): BigInt = {
    if (n < 1) 0
    else if (n == 1 || n == 2) 1
    else {
      var results: BigInt = 0
      if (mode) results = m2(n-2, !mode) + m2(n-2, !mode) + m2(n-3, !mode)
      if (!mode) results = m2(n-1, !mode) + m2(n-2, !mode)
      results
    }
  }

}