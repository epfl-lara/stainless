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
        unfolding(secretSauce(other))
        unfolding(oldBox.secretSauce(other))
        check(oldBox.secretSauce(other) + 1 == this.secretSauce(other))
      }
    }.ensuring(_ => old(this).secretSauce(other) + 1 == this.secretSauce(other))

    // What `increment` looks like after `AntiAliasing`
    @opaque @pure
    def incrementPure(): (Unit, Box) = {
      val newThis = Box(cnt + 1, other)
      ghostExpr {
        unfolding(newThis.secretSauce(other))
        unfolding(this.secretSauce(other))
        check(this.secretSauce(other) + 1 == newThis.secretSauce(other))
      }
      ((), newThis)
    }.ensuring { case (_, newThis) => this.secretSauce(newThis.other) + 1 == newThis.secretSauce(newThis.other) }
  }

  def test1(b: Box, cond: Boolean): Unit = {
    @ghost val oldBox = snapshot(b)
    val b2 = if (cond) b else Box(1, 1)
    b.increment()
    assert(oldBox.secretSauce(b.other) + 1 == b.secretSauce(b.other))
    assert(cond ==> (oldBox.secretSauce(b2.other) + 1 == b2.secretSauce(b.other)))
  }

  // What `test1` looks like after `AntiAliasing`
  def test1Pure(b: Box, cond: Boolean): Unit = {
    val oldBox = b
    val b2 = if (cond) b else Box(1, 1)
    val (_, newB) = b.incrementPure()
    val newB2 = if (cond) newB else b2
    assert(oldBox.secretSauce(newB.other) + 1 == newB.secretSauce(newB.other))
    assert(cond ==> (oldBox.secretSauce(newB2.other) + 1 == newB2.secretSauce(newB.other)))
  }

  def test2(b: Box, cond: Boolean): Unit = {
    val b2 = if (cond) b else Box(1, 1)
    @ghost val oldB2 = snapshot(b2)
    b2.increment()
    assert(oldB2.secretSauce(b2.other) + 1 == b2.secretSauce(b2.other))
    assert(cond ==> (oldB2.secretSauce(b.other) + 1 == b.secretSauce(b.other)))
  }

  // What `test2` looks like after `AntiAliasing`
  def test2Pure(b: Box, cond: Boolean): Unit = {
    val b2 = if (cond) b else Box(1, 1)
    val oldB2 = b2
    val (_, newB2) = b2.incrementPure()
    val newB = if (cond) newB2 else b
    assert(oldB2.secretSauce(newB2.other) + 1 == newB2.secretSauce(newB2.other))
    assert(cond ==> (oldB2.secretSauce(newB.other) + 1 == newB.secretSauce(newB.other)))
  }
}
