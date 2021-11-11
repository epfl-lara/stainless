import stainless.annotation._
import stainless.lang._

object StateTest {

  @cCode.`export`
  def main(): Int = {
    implicit val state = stainless.io.newState
    f()
  }

  def f()(implicit state: stainless.io.State): Int = {
    0
  }

}
