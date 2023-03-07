// Examples are figures from paper:
// Regression verification of unbalanced recursive functions with multiple calls (long version)
// https://arxiv.org/pdf/2207.14364.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object FibonacciUnused {

  // Fig. 13

  def t1(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n == 1) 1
    else t1(n - 1) + t1(n - 2)
  }

  def t2(n: BigInt): BigInt = {
    if (n < 1) 0
    else if (n == 1 || n == 2) 1
    else {
      var results: BigInt = 0
      var r1 = t2(n-1)
      var r2 = t2(n-2)
      var r3 = t2(n-3)
      if (n % 2 == 0) results = r2 + r2 + r3
      else results = r1 + r2
      results
    }
  }
}