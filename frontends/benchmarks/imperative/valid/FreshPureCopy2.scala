import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

object FreshPureCopy2 {
  @mutable case class Box(var x: BigInt) {
    @pure def pure_get(): BigInt = x
    def impure_update(newX: BigInt): Unit = {
      x = newX
    }
  }
  
  def f_immutable_type[A](a: A): Option[A] = Some(a)
  
  def test() = {
    val b = Box(0)
    val c = f_immutable_type(freshPureCopy(b))
    b.x = 1
    assert(c.get.get.x == 0)
    assert(b.x == 1)
  }
}
