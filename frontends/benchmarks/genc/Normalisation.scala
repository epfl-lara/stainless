import stainless.annotation._
import stainless.io._
import stainless.math.BitVectors._

object Normalisation {

  case class A(x: Int, y: UInt16, z: Int64) {
    require(
      x >= 0 && x < 1000 &&
      y >= 0 && y < 1000 &&
      z >= 0 && z < 1000
    )
    def sum: Int = x + y.toInt + z.toInt
  }
  case class B(a1: A, i: UInt8, j: UInt32, a2: A)

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a = A(100, 9, 200)
    val x = a.sum + a.sum
    val y = x + a.sum
    StdOut.println(y)
    val b = B(a, 76, 14, a)
    StdOut.println(b.a1.sum + b.i.toInt + b.j.toInt + b.a2.sum)
  }

}
