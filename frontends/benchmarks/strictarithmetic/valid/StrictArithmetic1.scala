
object StrictArithmetic1 {

  def foo1(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x << y
  }

  def fun1(x: Long, y: Int) = {
    require(0 <= y && y <= 63)
    x << y
  }

  def foo2(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x >> y
  }

  def fun2(x: Long, y: Int) = {
    require(0 <= y && y <= 63)
    x >> y
  }

  def foo3(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x >>> y
  }

  def fun3(x: Long, y: Int) = {
    require(0 <= y && y <= 63)
    x >>> y
  }

}

