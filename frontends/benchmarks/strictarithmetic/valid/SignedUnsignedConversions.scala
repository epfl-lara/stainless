import stainless.math.BitVectors
import stainless.math.BitVectors._

object SignedUnsignedConversions {
  def test1 = {
    val a: UInt3 = 3
    assert(a == a.toSigned[Int3].toUnsigned[UInt3])

    val b: UInt5 = 3
    assert(b == b.narrow[UInt2].widen[UInt5])

    val c : Int5 = 3
    assert(c == c.narrow[Int3].widen[Int5])
  }

  def test2(x: UInt8) = {
    assert(x == BitVectors.fromInt(x.toInt).toUnsigned[UInt32].narrow[UInt8])
  }

  def test3 = {
    val a = Array[Int](0, 100, 150, 132)
    val x0: UInt2 = 0
    val x1: UInt2 = 1
    val x2: UInt2 = 2
    val x3: UInt2 = 3
    assert(a(x0) == 0)
    assert(a(x1) == 100)
    assert(a(x2) == 150)
    assert(a(x3) == 132)

    val b = Array[Boolean](true, false, false, true)
    assert(b(x0))
    assert(!b(x1))
    assert(!b(x2))
    assert(b(x3))
  }
}
