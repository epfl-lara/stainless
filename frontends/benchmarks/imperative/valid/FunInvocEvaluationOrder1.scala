/* Copyright 2009-2019 EPFL, Lausanne */

object FunInvocEvaluationOrder1 {

  def test(): Int = {

    var res = 10
    justAddingStuff({
      res += 1
      res
    }, {
      res *= 2
      res
    }, {
      res += 10
      res
    })

    res
  } ensuring(_ == 32)

  def justAddingStuff(x: Int, y: Int, z: Int): Int = x + y + z

}
