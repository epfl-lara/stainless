object i1218 {
  case class B(var x: Int)

  def test(arr: Array[B]): Unit = {
    require(arr.length >= 2)
    val arr2 = arr.updated(1, B(42))
    // Illegal aliasing
    f(arr(0), arr2(0))
  }

  def f(b1: B, b2: B): Unit = {
    val x1 = b1.x
    b2.x = 50
    assert(b1.x == x1)
  }
}