import stainless.annotation._
import stainless.io._
import stainless.math.BitVectors._

object FixedArray {

  val CONSTANT1: UInt16 = 2
  val CONSTANT2: UInt16 = 3
  val CONSTANT3: UInt16 = CONSTANT1 + CONSTANT2

  @cCode.`export`
  case class W(x: Int, a: Array[Int], y: Int) {
    require(
      a.length == CONSTANT3.toInt &&
      0 <= x && x <= 1000 &&
      0 <= y && y <= 1000
    )
  }

  @cCode.`export`
  def f(w: W): Int = {
    require(0 <= w.a(0) && w.a(0) <= 1000)
    require(0 <= w.a(1) && w.a(1) <= 1000)
    require(0 <= w.a(2) && w.a(2) <= 1000)
    require(0 <= w.a(3) && w.a(3) <= 1000)
    require(0 <= w.a(4) && w.a(4) <= 1000)

    w.a(0) = 155

    w.a(0) + w.a(1) + w.a(2) + w.a(3) + w.a(4) + w.x + w.y
  }

  @cCode.`export`
  def g(a: Array[Int]): Unit = {
    require(a.length > 0)
    require(0 <= a(0) && a(0) <= 1000)

    a(0) += 1
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val w = W(30, Array(10, 20, 30, 20, 42), 100)
    val w2 = W(30, Array(10, 20, 30, 20, 42), { w.a(0) += 1; 100 })
    g(w.a)
    val a2 = w.a
    g(a2)
    val z = f(w)
    assert(z == 30 + 155 + 20 + 30 + 20 + 42 + 100)
    StdOut.println(z)
  }

}
