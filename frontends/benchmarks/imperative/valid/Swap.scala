import stainless.lang.swap

object Swap {
  def test(a1: Array[BigInt]): Unit = {
    require(a1.length > 10 && a1(2) == 200 && a1(4) == 500)

    swap(a1, 2, a1, 2)
    assert(a1(2) == 200)
    swap(a1, 2, a1, 4)
    assert(a1(2) == 500)
    assert(a1(4) == 200)
    swap(a1, 2, a1, 4)
    assert(a1(2) == 200)
    assert(a1(4) == 500)
  }

  def test2: Unit = {
    val a2 = Array(4, 8, 15, 16, 23, 42)

    swap(a2, 1, a2, 1)
    assert(a2(1) == 8)
    swap(a2, 0, a2, 5)
    assert(a2(0) == 42)
    assert(a2(1) == 8)
    assert(a2(2) == 15)
    assert(a2(3) == 16)
    assert(a2(4) == 23)
    assert(a2(5) == 4)
  }
}
