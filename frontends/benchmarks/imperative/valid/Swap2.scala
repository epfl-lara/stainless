import stainless.lang.swap

object Swap2 {

  case class Box(var x: BigInt)

  def test: Unit = {
    val a = Array[Box](Box(4), Box(8), Box(15), Box(16), Box(23), Box(42))
    swap(a, 2, a, 3)
    a(2).x *= 2
    a(3).x += 2
    assert(a(0).x == 4)
    assert(a(1).x == 8)
    assert(a(2).x == 32)
    assert(a(3).x == 17)
    assert(a(4).x == 23)
    assert(a(5).x == 42)
    swap(a, 2, a, 3)
    assert(a(2).x == 17)
    assert(a(3).x == 32)
    swap(a, 4, a, 3)
    assert(a(4).x == 32)
    assert(a(3).x == 23)
  }
}
