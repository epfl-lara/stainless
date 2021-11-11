import stainless.annotation._
import stainless.io._

object Pointer {

  case class Pointer[T](var x: T)

  def f(r: Pointer[Int], r2: Pointer[Int]): Unit = {
    r.x = 150
    r2.x = 250
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val r = Pointer(100)
    val r2 = Pointer(100)
    f(r, r2)
    assert(r.x == 150)
    assert(r2.x == 250)
    StdOut.println(r.x)
    StdOut.println(r2.x)
  }

}
