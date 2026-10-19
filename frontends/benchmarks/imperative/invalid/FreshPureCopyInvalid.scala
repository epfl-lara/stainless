import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

object FreshPureCopyInvalid {
  @mutable case class Box(var x: BigInt) {
    @pure def pure_get(): BigInt = x
    def impure_update(newX: BigInt): Unit = {
      x = newX
    }
  }
  
  def f_immutable_type[A](a: A): Option[A] = Some(a)
  
  def test() = {
    val b = Box(0)
    val c = freshPureCopy(b)
    c.get.impure_update(1)
    assert(c.get.pure_get() == 1)
  }
}
