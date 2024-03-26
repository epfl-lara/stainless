import stainless.lang.{ghost => ghostExpr, _}
import stainless.proof._
import stainless.annotation._
import StaticChecks._

object OpaqueMutation2 {
  case class SmallerBox(var otherCnt: BigInt)

  case class Box(var cnt: BigInt, var smallerBox: SmallerBox) {
    @opaque // Note the opaque
    def secretSauce(x: BigInt): BigInt = cnt + x // Nobody thought of it!

    @opaque // Note the opaque here as well
    def increment(): Unit = {
      @ghost val oldBox = snapshot(this)
      cnt += 1
      ghostExpr {
        unfold(secretSauce(smallerBox.otherCnt))
        unfold(oldBox.secretSauce(smallerBox.otherCnt))
        check(oldBox.secretSauce(smallerBox.otherCnt) + 1 == this.secretSauce(smallerBox.otherCnt))
      }
    }.ensuring(_ => old(this).secretSauce(smallerBox.otherCnt) + 1 == this.secretSauce(smallerBox.otherCnt))
  }

  def test(b: Box): Unit = {
    @ghost val oldBox = snapshot(b)
    b.increment()
    // Note that, even though the implementation of `increment` does not alter `smallerBox`,
    // we do not have that knowledge here since the function is marked as opaque.
    // Therefore, the following is incorrect (but it holds for `b.other`, see the other `valid/OpaqueMutation`)
    assert(oldBox.secretSauce(oldBox.smallerBox.otherCnt) + 1 == b.secretSauce(oldBox.smallerBox.otherCnt))
  }
}