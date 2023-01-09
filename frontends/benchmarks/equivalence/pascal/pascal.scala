// Examples are figures from paper:
// Regression verification of unbalanced recursive functions with multiple calls (long version)
// https://arxiv.org/pdf/2207.14364.pdf

import stainless.collection._
import stainless.lang._
import stainless.annotation._

object Pascal {

  // Fig. 8
  // RVT times out due to KLEE timing out when trying to prove the base-case

  def p1(n: BigInt, m: BigInt): BigInt = {
    if (m < 1 || n < 1 || m > n) 0
    else if (m == 1 || n == 1 || m == n) 1
    else p1(n-1, m-1) + p1(n-1, m)
  }

  def p2(n: BigInt, m: BigInt): BigInt = {
    if (m < 1 || n < 1 || m > n) 0
    else if (m == 1 || n == 1 || m == n) 1
    else p2(n-1, m-1) + p2 (n-2 , m-1) + p2 (n-2 , m)
  }
}