import stainless.annotation._

case class InvalidInternallyMutable(@internallyMutable var x: Int) {
  def setX(newX: Int): Unit = {
    x = newX
  }
}