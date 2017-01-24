/* Copyright 2009-2016 EPFL, Lausanne */

object NestedFunState6 {

  def simpleSideEffect(n: BigInt): BigInt = {
    require(n > 0)

    var a = BigInt(0)

    def incA(prevA: BigInt): Unit = {
      require(prevA == a)
      a += 1
    } ensuring(_ => a == prevA + 1)

    incA(a)
    incA(a)
    incA(a)
    incA(a)
    a
  } ensuring(_ == 4)

}
