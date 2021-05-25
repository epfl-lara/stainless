import stainless.annotation._

object WhileInLet {

  @export
  def main(): Unit = {
    val noLoop = while (false) {}
    ()
  }

}
