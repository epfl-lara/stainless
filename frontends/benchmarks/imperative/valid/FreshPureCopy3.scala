import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

object FreshPureCopy3 {
  @mutable case class Box(var x: BigInt) {
    @pure def pure_get(): BigInt = x
    def impure_update(newX: BigInt): Unit = {
      x = newX
    }
  }
  
  def test() = {
    val b = Box(0)
    val immut_b = freshPureCopy(b)
    b.get.impure_update(1)
    assert(immut_b.get.pure_get() == 0)
    assert(b.x == 1)
  }
}
