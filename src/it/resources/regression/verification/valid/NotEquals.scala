/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object NotEquals { 

  // Represents n/d
  case class Q(n: BigInt, d: BigInt)

  def op(a: Q, b: Q) = {
    require(isRational(a) && isRational(b))

    Q(a.n + b.n, a.d)
  } ensuring {
    isRational(_)
  }

  //def isRational(a: Q) = a.d != 0
  def isRational(a: Q) = a.d != 0

}
