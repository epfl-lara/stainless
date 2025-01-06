object NewArrayNonPrimitive {
  def test(len: Int): Unit = {
    require(len >= 0)
    // Cannot use array constructor for non-primitive type String
    val arr = new Array[String](len)
  }
}