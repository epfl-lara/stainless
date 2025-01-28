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
        unfolding(secretSauce(smallerBox.otherCnt))
        unfolding(oldBox.secretSauce(smallerBox.otherCnt))
        check(oldBox.secretSauce(smallerBox.otherCnt) + 1 == this.secretSauce(smallerBox.otherCnt))
      }
   }.ensuring(_ => old(this).secretSauce(smallerBox.otherCnt) + 1 == this.secretSauce(smallerBox.otherCnt))
  }

  def test1(b: Box, cond: Boolean): Unit = {
    @ghost val oldBox = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123))
    val smallerBoxAlias = b.smallerBox
    b.increment()
    assert(b.smallerBox.otherCnt == smallerBoxAlias.otherCnt)
    assert(oldBox.secretSauce(b.smallerBox.otherCnt) + 1 == b.secretSauce(b.smallerBox.otherCnt))
    assert(oldBox.secretSauce(smallerBoxAlias.otherCnt) + 1 == b.secretSauce(smallerBoxAlias.otherCnt))
    assert(cond ==> (oldBox.secretSauce(b2.smallerBox.otherCnt) + 1 == b2.secretSauce(b.smallerBox.otherCnt)))
    assert(cond ==> (oldBox.secretSauce(smallerBoxAlias.otherCnt) + 1 == b2.secretSauce(smallerBoxAlias.otherCnt)))
  }

  def test2(b: Box, cond: Boolean): Unit = {
    val b2 = if (cond) b else Box(1, SmallerBox(123))
    @ghost val oldB2 = snapshot(b2)
    b2.increment()
    assert(oldB2.secretSauce(b2.smallerBox.otherCnt) + 1 == b2.secretSauce(b2.smallerBox.otherCnt))
    assert(cond ==> (oldB2.secretSauce(b.smallerBox.otherCnt) + 1 == b.secretSauce(b.smallerBox.otherCnt)))
  }
}
