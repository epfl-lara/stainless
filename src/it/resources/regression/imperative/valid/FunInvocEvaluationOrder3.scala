/* Copyright 2009-2016 EPFL, Lausanne */

object FunInvocEvaluationOrder3 {

  def leftToRight(n: BigInt): BigInt = {
    require(n > 0)

    var a = BigInt(0)

    def nested(x: BigInt, y: BigInt): Unit = {
      a = x + y
    }

    nested({a += 10; a}, {a *= 2; a})
    a

  } ensuring(_ == 30)

}
