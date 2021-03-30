import stainless.math.BitVectors._

object BitVectors3 {

  def test1(x: UInt42): Unit = {
    assert(x.toSigned[Int42].toUnsigned[UInt42] == x)
  }

  def test2(a: Array[Boolean], x: UInt8): Unit = {
    require(a.length > 1 && a(1) && x == 1)

    assert(a(x.widen[UInt32].toSigned[Int32].toInt))
  }

  def test3: Unit = {
    val x: UInt8 = 255
    assert(x.toSigned[Int8] == -1)
  }

}
