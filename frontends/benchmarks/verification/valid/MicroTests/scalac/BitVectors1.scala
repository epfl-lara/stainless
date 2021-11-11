import stainless.math.BitVectors._

object BitVectors1 {

  def test1(n1: UInt3, n2: UInt3, n3: UInt3) = {
    require(n2 <= n3 && n1 <= n3 - n2 && n1 + n2 == n3)

    assert(n3 - n1 == n2)
  }

  def test2(n: UInt10) = {
    assert((n ^ n) == 0)
  }

  def test3(n: UInt100) = {
    assert((n & n) == n)
    assert((n & 0) == 0)
  }

  def test4(n: UInt200) = {
    assert((n | n) == n)
    assert((n | 0) == n)
  }

  def test5(n1: UInt200, n2: UInt200) = {
    require(n1 > n2)
    assert(n2 < n1)
  }

  def test6(n1: UInt200, n2: UInt200) = {
    require(n1 > n2)
    assert(n1 >= n2 + 1)
  }

  def test7(n1: UInt5, n2: UInt5, n3: UInt5) = {
    require(n2 != 0 && n1 <= n3 / n2 && n1 * n2 == n3)
    assert(n1 == n3 / n2)
  }

  def test8(n: UInt100) = {
    assert(n % 2 == (n mod 2))
    assert(n % 2 == 0 || n % 2 == 1)
  }

  def test9(n: UInt100) = {
    assert(n >>> 1 == n / 2)
  }

  def test10() = {
    assert(min[UInt3] == 0)
    assert(max[UInt3] == 7)
  }

  def test11(n: UInt100) = {
    require(n <= max[UInt100] / 2)
    assert(n << 1 == n * 2)
  }

  def test12(n: UInt100) = {
    require(n < max[UInt100] / 2)
    assert(n >> 1 == n / 2)
  }

  def test13(n: UInt10) = {
    require(n == 42)
    val m = n.widen[UInt14]
    assert(m == 42)
  }

  def test14(n: UInt10) = {
    require(n == 42)
    val m = n.narrow[UInt3]
    assert(m == 2)
  }

  def test15() = {
    val zero: UInt32 = 0
    assert(~zero == max[UInt32])
  }

  def test16(n: UInt32) = {
    assert(~(~n) == n)
  }

}
