import stainless.annotation._
import stainless.lang._

object StateTest {

  @extern
  def main(args: Array[String]): Unit = _main()

  def _main(): Int = {
    implicit val state = stainless.io.newState
    f()
  }

  def f()(implicit state: stainless.io.State): Int = {
    0
  }

}
