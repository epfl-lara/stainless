import stainless.lang._
import stainless.annotation._

object ExternMut {

  trait Test {
    def something: BigInt
  }

  @extern
  case class Box(value: BigInt) extends Test {
    def something: BigInt = 42
  }

  def test(b: Box) = {
    val x = b.something
    assert(x == 42) // fails
  }

}
