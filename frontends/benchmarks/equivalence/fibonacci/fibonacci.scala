// Examples are figures from paper:
// Regression verification of unbalanced recursive functions with multiple calls (long version)
// https://arxiv.org/pdf/2207.14364.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Fibonacci {

  // Fig. 4

  def f1(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n <= 2) 1
    else f1(n-1) + f1(n-2)
  }

  def f2(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n <= 2) 1
    else f2(n-2) + f2(n-2) + f2(n-3)
  }
}