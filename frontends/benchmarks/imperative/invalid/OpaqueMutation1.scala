import stainless.lang.{ghost => ghostExpr, _}
import stainless.proof._
import stainless.annotation._
import StaticChecks._

object OpaqueMutation1 {

  case class Box(var cnt: BigInt, var other: BigInt) {
    @opaque // Note the opaque
    def secretSauce(x: BigInt): BigInt = cnt + x // Nobody thought of it!

    @opaque // Note the opaque here as well
    def increment(): Unit = {
      @ghost val oldBox = snapshot(this)
      cnt += 1
      ghostExpr {
        unfold(secretSauce(other))
        unfold(oldBox.secretSauce(other))
        check(oldBox.secretSauce(other) + 1 == this.secretSauce(other))
      }
    }.ensuring(_ => old(this).secretSauce(other) + 1 == this.secretSauce(other))
  }

  def test(b: Box): Unit = {
    @ghost val oldBox = snapshot(b)
    b.increment()
    // Note that, even though the implementation of `increment` does not alter `other`,
    // we do not have that knowledge here since the function is marked as opaque.
    // Therefore, the following is incorrect (but it holds for `b.other`, see the other `valid/OpaqueMutation`)
    assert(oldBox.secretSauce(oldBox.other) + 1 == b.secretSauce(oldBox.other))
  }
}