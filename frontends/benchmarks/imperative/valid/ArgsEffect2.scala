import stainless.annotation._

object ArgsEffect2 {

  case class MutClass(var i: BigInt) {
    def inc: MutClass = {
      i += 1
      this
    }
    @pure
    def isEqual(j: BigInt): Boolean = i == j
  }

  def test(mc: MutClass): Unit = {
    val old = mc.i
    val res = mc.inc.isEqual(old + 1)
    assert(res)
  }
}