import stainless.lang.{ghost => ghostExpr, _}
import stainless.lang.StaticChecks._
import stainless.annotation._
object GhostExternNotChecked {

  @ghost
  def f(): BigInt = {
    val a: BigInt = 1
    a
  }

  @extern
  def externGhost(): Unit = {
    // Can call a ghost function from an extern function, even if one should not
    val a = f()
  }
}
