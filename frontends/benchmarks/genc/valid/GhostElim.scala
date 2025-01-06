import stainless._
import stainless.proof._
import stainless.lang.{ghost => ghostExpr, _}
import stainless.annotation.{wrapping => _, _}
import StaticChecks._

object GhostElim {
  @ghost
  def thisIsGhost(x: Int): Int = 3

  @ghost
  def ghostProp(x: Int): Boolean = x <= 100

  @cCode.`export`
  def test(x: Int): Unit = {
    require(x <= 42)
    ghostExpr {
      thisIsGhost(x)
      thisIsGhost(x)
      check(ghostProp(x))
      thisIsGhost(x)
      ()
    }
  }

  @cCode.`export`
  def main(): Unit = ()
}