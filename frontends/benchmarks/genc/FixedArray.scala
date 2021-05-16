import stainless.annotation._
import stainless.io._
import stainless.math.BitVectors._

object FixedArray {

  val CONSTANT1: UInt16 = 5
  val CONSTANT2: UInt16 = 12
  val CONSTANT3: UInt16 = CONSTANT1 + CONSTANT2

  @export
  case class W(x: Int, a: Array[Int], y: Int) {
    require(
      a.length == CONSTANT3.toInt &&
      0 <= x && x <= 1000 &&
      0 <= y && y <= 1000
    )
  }

  @export
  def f(w: W): Int = {
    require(0 <= w.a(0) && w.a(0) <= 1000)
    require(0 <= w.a(1) && w.a(1) <= 1000)
    require(0 <= w.a(2) && w.a(2) <= 1000)
    require(0 <= w.a(3) && w.a(3) <= 1000)
    require(0 <= w.a(4) && w.a(4) <= 1000)

    w.a(0) = 155

    w.a(0) + w.a(1) + w.a(2) + w.a(3) + w.a(4) + w.x + w.y
  }

  @export
  def main(): Unit = {
  }

}
