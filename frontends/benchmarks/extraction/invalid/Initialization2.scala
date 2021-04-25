object Initialization2 {
  case class Hello() {
    val message = answer + 3
    val answer = 42
  }
  def getM: Int = {
    new Hello().message
  } ensuring (_ == 45)
}
