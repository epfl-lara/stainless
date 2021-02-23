import stainless.lang._
import stainless.annotation._

case class A(var x: BigInt)
trait B { var a: A }

object Test {
  def test(b: B): Unit = {
    val a = b.a
    0
  }
}
