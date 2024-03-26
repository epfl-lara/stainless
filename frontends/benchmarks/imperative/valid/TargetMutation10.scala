import stainless.lang.{ghost => ghostExpr, _}
import stainless.proof._
import stainless.annotation._
import StaticChecks._

object TargetMutation10 {
  case class EvenSmallerBox(var lastCnt: BigInt)

  case class SmallerBox(var otherCnt: BigInt, var evenSmallerBox: EvenSmallerBox) {
    def increment(): Unit = {
      otherCnt += 1
      evenSmallerBox.lastCnt += 1
    }
  }

  case class Box(var cnt: BigInt, var smallerBox: SmallerBox) {
    def increment(): Unit = {
      cnt += 1
      smallerBox.otherCnt += 1
      smallerBox.evenSmallerBox.lastCnt += 1
    }
    def replaceSmallerBox(): Unit = {
      cnt += 1
      smallerBox = SmallerBox(-1, EvenSmallerBox(-2))
    }
  }

  def test1(b: Box, cond: Boolean): Unit = {
    @ghost val oldBox = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    val smallerBoxAlias = b.smallerBox
    val smallerBoxAlias2 = if (cond) b.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)
    b.increment()
    assert(cond ==> (b2.cnt == b.cnt))
    assert(!cond ==> (b2.cnt == 1))
    assert(oldBox.cnt + 1 == b.cnt)
    assert(b.smallerBox.otherCnt == smallerBoxAlias.otherCnt)
    assert(b.smallerBox.evenSmallerBox.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(evenSmallerBoxAliasBis.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(cond ==> (b2.smallerBox.otherCnt == smallerBoxAlias.otherCnt))
    assert(cond ==> (evenSmallerBoxAlias2.lastCnt == b.smallerBox.evenSmallerBox.lastCnt))
    assert(evenSmallerBoxAlias2.lastCnt == evenSmallerBoxAlias2Bis.lastCnt)
    assert(!cond ==> (b2.smallerBox.otherCnt == 123))
    assert(!cond ==> (evenSmallerBoxAlias2.lastCnt == 456))
    assert(cond ==> (smallerBoxAlias2.otherCnt == b.smallerBox.otherCnt))
    assert(!cond ==> (smallerBoxAlias2.otherCnt == 456))
  }

  def test2(b: Box, cond: Boolean): Unit = {
    @ghost val oldb = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    @ghost val oldb2 = snapshot(b2)
    val smallerBoxAlias = b.smallerBox
    val smallerBoxAlias2 = if (cond) b.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)
    b2.increment()
    assert(cond ==> (b2.cnt == b.cnt))
    assert(!cond ==> (b2.cnt == 2))
    assert(!cond ==> (oldb.cnt == b.cnt))
    assert(b.smallerBox.otherCnt == smallerBoxAlias.otherCnt)
    assert(b.smallerBox.evenSmallerBox.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(evenSmallerBoxAliasBis.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(cond ==> (b2.smallerBox.otherCnt == smallerBoxAlias.otherCnt))
    assert(cond ==> (evenSmallerBoxAlias2.lastCnt == b.smallerBox.evenSmallerBox.lastCnt))
    assert(evenSmallerBoxAlias2.lastCnt == evenSmallerBoxAlias2Bis.lastCnt)
    assert(!cond ==> (b.smallerBox.otherCnt == oldb.smallerBox.otherCnt))
    assert(cond ==> (smallerBoxAlias2.otherCnt == b.smallerBox.otherCnt))
  }

  def test3(b: Box, cond: Boolean): Unit = {
    @ghost val oldBox = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    val smallerBoxAlias = b.smallerBox
    val smallerBoxAlias2 = if (cond) b.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)
    b.smallerBox.increment()
    assert(b.smallerBox.otherCnt == smallerBoxAlias.otherCnt)
    assert(b.smallerBox.evenSmallerBox.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(evenSmallerBoxAliasBis.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(cond ==> (b2.smallerBox.otherCnt == smallerBoxAlias.otherCnt))
    assert(cond ==> (evenSmallerBoxAlias2.lastCnt == b.smallerBox.evenSmallerBox.lastCnt))
    assert(evenSmallerBoxAlias2.lastCnt == evenSmallerBoxAlias2Bis.lastCnt)
    assert(!cond ==> (b2.smallerBox.otherCnt == 123))
    assert(!cond ==> (evenSmallerBoxAlias2.lastCnt == 456))
    assert(cond ==> (smallerBoxAlias2.otherCnt == b.smallerBox.otherCnt))
    assert(!cond ==> (smallerBoxAlias2.otherCnt == 456))
  }

  def test4(b: Box, cond: Boolean): Unit = {
    @ghost val oldb = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    @ghost val oldb2 = snapshot(b2)
    val smallerBoxAlias = b.smallerBox
    val smallerBoxAlias2 = if (cond) b.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)
    b2.smallerBox.increment()
    assert(b.smallerBox.otherCnt == smallerBoxAlias.otherCnt)
    assert(b.smallerBox.evenSmallerBox.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(evenSmallerBoxAliasBis.lastCnt == evenSmallerBoxAlias.lastCnt)
    assert(cond ==> (b2.smallerBox.otherCnt == smallerBoxAlias.otherCnt))
    assert(cond ==> (evenSmallerBoxAlias2.lastCnt == b.smallerBox.evenSmallerBox.lastCnt))
    assert(evenSmallerBoxAlias2.lastCnt == evenSmallerBoxAlias2Bis.lastCnt)
    assert(!cond ==> (b.smallerBox.otherCnt == oldb.smallerBox.otherCnt))
    assert(cond ==> (smallerBoxAlias2.otherCnt == b.smallerBox.otherCnt))
  }

  def test5(b: Box, cond: Boolean): Unit = {
    @ghost val oldBox = snapshot(b)
    val oldOtherCnt = b.smallerBox.otherCnt
    val oldLastCnt = b.smallerBox.evenSmallerBox.lastCnt
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    val smallerBoxAlias = b.smallerBox
    val smallerBoxAlias2 = if (cond) b.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)

    b.replaceSmallerBox()

    assert(cond ==> (b2.cnt == b.cnt))
    assert(!cond ==> (b2.cnt == 1))
    assert(oldBox.cnt + 1 == b.cnt)

    assert(b.smallerBox.otherCnt == -1)
    assert(b.smallerBox.evenSmallerBox.lastCnt == -2)

    assert(oldBox.smallerBox.otherCnt == oldOtherCnt)
    assert(oldBox.smallerBox.evenSmallerBox.lastCnt == oldLastCnt)

    assert(smallerBoxAlias.otherCnt == oldOtherCnt)
    assert(evenSmallerBoxAlias.lastCnt == oldLastCnt)

    assert(cond ==> (smallerBoxAlias.otherCnt == oldOtherCnt))
    assert(cond ==> (evenSmallerBoxAlias.lastCnt == oldLastCnt))
    assert(cond ==> (b2.smallerBox.otherCnt == -1))
    assert(cond ==> (b2.smallerBox.evenSmallerBox.lastCnt == -2))

    assert(!cond ==> (b2.smallerBox.otherCnt == 123))
    assert(!cond ==> (evenSmallerBoxAlias2.lastCnt == 456))
    assert(!cond ==> (smallerBoxAlias2.otherCnt == 456))
  }

  def test6(b: Box, cond: Boolean): Unit = {
    @ghost val oldb = snapshot(b)
    val b2 = if (cond) b else Box(1, SmallerBox(123, EvenSmallerBox(10)))
    val oldOtherCnt = b2.smallerBox.otherCnt
    val oldLastCnt = b2.smallerBox.evenSmallerBox.lastCnt
    @ghost val oldb2 = snapshot(b2)
    val smallerBoxAlias = b2.smallerBox
    val smallerBoxAlias2 = if (cond) b2.smallerBox else SmallerBox(456, EvenSmallerBox(20))
    val evenSmallerBoxAlias = b2.smallerBox.evenSmallerBox
    val evenSmallerBoxAliasBis = smallerBoxAlias.evenSmallerBox
    val evenSmallerBoxAlias2 = if (cond) b2.smallerBox.evenSmallerBox else EvenSmallerBox(456)
    val evenSmallerBoxAlias2Bis = if (cond) smallerBoxAlias.evenSmallerBox else EvenSmallerBox(456)

    b2.replaceSmallerBox()

    assert(cond ==> (b2.cnt == b.cnt))
    assert(oldb2.cnt + 1 == b2.cnt)

    assert(b2.smallerBox.otherCnt == -1)
    assert(b2.smallerBox.evenSmallerBox.lastCnt == -2)
    assert(cond ==> (b.smallerBox.otherCnt == -1))
    assert(cond ==> (b.smallerBox.evenSmallerBox.lastCnt == -2))

    assert(oldb2.smallerBox.otherCnt == oldOtherCnt)
    assert(oldb2.smallerBox.evenSmallerBox.lastCnt == oldLastCnt)

    assert(smallerBoxAlias.otherCnt == oldOtherCnt)
    assert(evenSmallerBoxAlias.lastCnt == oldLastCnt)

    assert(cond ==> (smallerBoxAlias.otherCnt == oldOtherCnt))
    assert(cond ==> (evenSmallerBoxAlias.lastCnt == oldLastCnt))

    assert(!cond ==> (evenSmallerBoxAlias2.lastCnt == 456))
    assert(!cond ==> (smallerBoxAlias2.otherCnt == 456))
  }

}