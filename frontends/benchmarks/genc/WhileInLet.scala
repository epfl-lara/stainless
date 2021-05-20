import stainless.annotation._

object WhileInLet {

  @export
  def whileInLet(): Unit = {
    val noLoop = while (false) {}
    ()
  }

}
