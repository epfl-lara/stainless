import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
object GhostExtern {

  def f(): Unit = {
    val a = 1
    ghostExpr {
      externGhost()
    }
    ()
  }

  @extern @ghost
  def externGhost(): Unit = {
    println("Hello")
  }
}
