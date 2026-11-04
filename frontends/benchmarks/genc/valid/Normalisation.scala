import stainless.annotation._
import stainless.io._
import stainless.math.Unsigned._

object Normalisation {

  case class A(x: Int, y: UShort, z: Long) {
    require(
      x >= 0 && x < 1000 &&
      y >= 0.toUShort && y < 1000.toUShort &&
      z >= 0 && z < 1000
    )
    def sum: Int = x + y.toInt + z.toInt
  }
  case class B(a1: A, i: UByte, j: UInt, a2: A)

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    val a = A(100, 9.toUShort, 200)
    val x = a.sum + a.sum
    val y = x + a.sum
    StdOut.println(y)
    val b = B(a, 76.toUByte, 14.toUInt, a)
    StdOut.println(b.a1.sum + b.i.toInt + b.j.toInt + b.a2.sum)
  }

}
