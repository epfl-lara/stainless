import stainless.annotation._
import stainless.io._

object ArgumentsEffects {

  def f(x1: Int, x2: Int, x3: Int)(implicit @ghost state: State): Unit = {
    require(x1 == 1)
    require(x2 == 1)
    require(x3 == 3)
    StdOut.print(x1)
    StdOut.print(x2)
    StdOut.println(x3)
  }

  @cCode.`export`
  def main()(implicit @ghost state: State): Unit = {
    var x = 0

    f({x += 1; x}, x, {x+= 2; x })
  }

}
