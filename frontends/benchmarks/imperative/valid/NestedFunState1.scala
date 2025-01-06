/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object NestedFunState1 {

  def sum(n: BigInt): BigInt = {
    require(n > 0)
    var i = BigInt(0)
    var res = BigInt(0)

    def iter(): Unit = {
      require(res >= i && i >= 0 && n >= i)
      decreases(n - i)
      if(i < n) {
        i += 1
        res += i
        iter()
      }
   }.ensuring(_ => res >= n)

    iter()
    res
 }.ensuring(_ >= n)

}
