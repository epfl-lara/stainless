object ReturnWithMutation2 {
  def f(cond: Boolean, array: Array[Int]): Int = {
    require(array.length > 0)
    if (cond) return 10
    array(0) = 100
    array(0)
  }

  def test: Unit = {
    assert(f(true, Array(200)) == 10)
    assert(f(false, Array(200)) == 100)
  }
}
