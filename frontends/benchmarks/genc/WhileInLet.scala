import stainless.annotation._

object WhileInLet {

  @cCode.`export`
  def main(): Unit = {
    val noLoop = while (false) {}
    ()
  }

}
