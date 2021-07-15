object ArrayAccess {
  def zero: Int = 0

  def reset(a: Array[Int]): Unit = {
    require(a.length > 0)
    a(zero) = 0
    a(0) = 0
  }
}
