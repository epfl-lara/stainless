package test.resources.regression.verification.purescala.invalid

object AddingNegativeNumbers {

  def additionOverflow(x: Int, y: Int): Int = {
    require(x <= 0 && y <= 0)
    x + y
  } ensuring(_ <= 0)

}
