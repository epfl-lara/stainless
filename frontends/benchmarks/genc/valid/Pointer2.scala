import stainless.annotation._
import stainless.io._

object Pointer2 {

  case class Pointer[T](var x: T)

  def inc(p: Pointer[Int]): Int = {
    require(0 <= p.x && p.x <= 1000)
    p.x += 1
    p.x
  }

  def f(v: Int): Int = {
    require(0 <= v && v <= 500)
    inc(Pointer(v + 42))
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val res1 = inc(Pointer(123))
    assert(res1 == 124)
    val res2 = f(400)
    assert(res2 == 443)
    StdOut.println(res1)
    StdOut.println(res2)
  }
}
