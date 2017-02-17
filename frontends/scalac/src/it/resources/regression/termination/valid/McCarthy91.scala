/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

/*
This function terminates for all inputs, see
http://en.wikipedia.org/wiki/McCarthy_91_function
*/
object McCarthy91 {
  def M(n: BigInt): BigInt = {
    decreases(101 - n)
    if (n > 100) n - 10 else M(M(n + 11))
  } ensuring (_ == (if (n > 100) n - 10 else BigInt(91)))
}
