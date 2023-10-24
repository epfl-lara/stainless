object NewArrayPrimitive {
  def test0(len: Int): Unit = {
    require(len >= 0)
    val arr = new Array[Long](len)
    if (len > 0) {
      assert(arr(len - 1) == (0 : Long))
    }
  }

  def test1(len: Int): Unit = {
    require(len >= 0)
    val arr = new Array[Int](len)
    if (len > 0) {
      assert(arr(len - 1) == 0)
    }
  }

  def test2(len: Int): Unit = {
    require(len >= 0)
    val arr = new Array[Short](len)
    if (len > 0) {
      assert(arr(len - 1) == (0 : Short))
    }
  }

  def test3(len: Int): Unit = {
    require(len >= 0)
    val arr = new Array[Byte](len)
    if (len > 0) {
      assert(arr(len - 1) == (0 : Byte))
    }
  }

  def test4(len: Int): Unit = {
    require(len >= 0)
    val arr = new Array[Char](len)
    if (len > 0) {
      assert(arr(len - 1) == (0 : Char))
    }
  }

}