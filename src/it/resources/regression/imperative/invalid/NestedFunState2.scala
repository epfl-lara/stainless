/* Copyright 2009-2016 EPFL, Lausanne */

object NestedFunState2 {

  def sum(n: BigInt): BigInt = {
    require(n > 0)
    var i = BigInt(0)
    var res = BigInt(0)

    def iter(): Unit = {
      require(res >= i && i >= 0)
      if(i < n) {
        i += 1
        res += i
        iter()
      }
    }

    iter()
    res
  } ensuring(_ < 0)

}
