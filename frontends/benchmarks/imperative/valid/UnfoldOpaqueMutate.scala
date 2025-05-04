import stainless.lang._
import stainless.annotation._
import StaticChecks._

object UnfoldOpaqueMutate {
  case class Box(var cnt: BigInt)

  case class WrappedBox(var box: Box) {
    @opaque
    def opaqueMutMeth1(x: BigInt): Unit = {
      box.cnt += x
    }

    @opaque
    def opaqueMutMeth2(x: BigInt): Unit = {
      box = Box(x * 2)
    }
  }

  def test1(wb: WrappedBox, x: BigInt): Unit = {
    @ghost val oldWb = snapshot(wb)
    unfolding(wb.opaqueMutMeth1(x))
    assert(wb.box.cnt == oldWb.box.cnt + x)
  }

  def test2(wb: WrappedBox, x: BigInt): Unit = {
    unfolding(wb.opaqueMutMeth2(x))
    assert(wb.box == Box(x * 2))
  }
}
