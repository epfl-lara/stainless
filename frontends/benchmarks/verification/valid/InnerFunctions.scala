// Testing FunctionClosure captures for PC variables
object InnerFunctions {

  def outer1(x: BigInt): Unit = {
    require(x >= 0)
    def inner1(): Unit = ()
  }

  def outer2(x: BigInt): Unit = {
    val y = x
    val z = y
    def inner2(a: BigInt): Unit = ()
  }

  def outer3(x: BigInt, a: BigInt): Unit = {
    require(x >= 0 && a >= x)
    def inner3(y: BigInt): Unit = {
      val b = a
      assert(a >= 0)
      assert(b >= 0)
    }
  }

  def outer4(x: BigInt): Unit = {
    require(x >= 0)
    val a = x - 2
    def inner4(y: BigInt): Unit = {
      val b = a
      assert(a >= -2)
      assert(b >= -2)
    }
  }

  def outer5(x: BigInt, y: BigInt, z: BigInt) = {
    require(0 <= x && x <= y)
    require(z >= 42)
    val a = x + 1
    def inner5A = {
      val aa = a + 1
      assert(aa >= 2)
    }
    def inner5B = {
      val yy = y
      assert(yy >= 0)
    }
  }

  def outer6(x: BigInt, y: BigInt, z: BigInt) = {
    require(0 <= x && x <= y)
    require(z >= 42)
    val a = x + 1
    def inner6A = { val aa = a + 1 }
    def inner6B = { val yy = y }
  }

  def outer7(x: BigInt): Unit = {
    require(0 < x && x < 10)
    val y = x
    val z = y + 10
    def inner7(w: BigInt): Unit = {
      require(w < z)
      assert(w < 20)
    }
  }
}