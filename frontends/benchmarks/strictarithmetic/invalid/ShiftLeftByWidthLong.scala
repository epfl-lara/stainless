
object ShiftLeftByWidthLong {

  def f(x: Long, y: Int) = {
    require(0 <= y && y <= 64)
    x << y
  }

}
