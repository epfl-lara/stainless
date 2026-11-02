
object ShiftRightByWidthInt {

  def f(x: Int, y: Int) = {
    require(0 <= y && y <= 32)
    x >> y
  }

}
