import stainless.math.BitVectors._

object BitVectors2 {

  def test1(n1: Int3, n2: Int3, n3: Int3) = {
    require(n2 >= 0 && n2 <= n3 && n1 <= n3 - n2 && n1 + n2 == n3)

    assert(n3 - n1 == n2)
  }

  def test2(n: Int10) = {
    assert((n ^ n) == 0)
  }

  def test3(n: Int100) = {
    assert((n & n) == n)
    assert((n & 0) == 0)
  }

  def test4(n: Int200) = {
    assert((n | n) == n)
    assert((n | 0) == n)
  }

  def test5(n1: Int200, n2: Int200) = {
    require(n1 > n2)
    assert(n2 < n1)
  }

  def test6(n1: Int200, n2: Int200) = {
    require(n1 > n2)
    assert(n1 >= n2 + 1)
  }

  def test8(n: Int100) = {
    require(n < 0)
    assert(n % 2 == -(n mod 2))
    assert(n % 2 == 0 || n % 2 == -1)
  }

  def test10() = {
    assert(min[Int3] == -4)
    assert(max[Int3] == 3)
  }

  def test11(n: Int100) = {
    require(0 <= n && n <= max[Int100] / 2)
    assert(n << 1 == n * 2)
  }

  def test12(n: Int100) = {
    require(0 <= n && n < max[Int100] / 2)
    assert(n >> 1 == n / 2)
  }

  def test13(n: Int10) = {
    require(n == 42)
    val m = n.widen[Int14]
    assert(m == 42)
  }

  def test14(n: Int4) = {
    require(n == 7)
    val m = n.narrow[Int3]
    assert(m == -1)
  }

}
