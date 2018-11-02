import stainless.annotation._

object Purity2 {

  case class Box(var value: BigInt) {
    def setMe(x: BigInt): Unit = {
      value = x
    }
  }

  def noMutation(@pure box: Box): Boolean = {
    box.value > 0
  }

  def mutation(@pure box: Box): Boolean = {
    doStuff(box)
    true
  }

  def doStuff(box: Box): Unit = {
    box.setMe(42)
  }

}
