
object BoundedProducts {

  // Products of bounded operands: the multiplication overflow checks are easy for the solvers when the
  // product is computed on twice the width (they timed out when they were checked with a division).
  def area(w: Int, h: Int): Int = {
    require(0 <= w && w <= 512 && 0 <= h && h <= 512)
    w * h
  }

  def areaLong(w: Long, h: Long): Long = {
    require(0 <= w && w <= 512 && 0 <= h && h <= 512)
    w * h
  }

  def term(component: Int, coefficient: Byte): Int = {
    require(0 <= component && component <= 255)
    component * coefficient.toInt
  }

  def square(x: Int): Int = {
    require(-46340 <= x && x <= 46340) // 46340^2 < 2^31 <= 46341^2
    x * x
  }

}
