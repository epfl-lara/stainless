object Int2Arithmetic {
  val a: Int = 1
  val c: Int = a + b

  def add(x: Int, y: Int): Int = {
    x + y
  }

  def sub(x:Int, y: Int): Int = {
    x - y
  }

  def mul(x: Int, y: Int): Int = {
    x * y
  }

  def div(x: Int, y: Int): Int = {
    x / y
  }

  def mod(x: Int, y: Int): Int = {
    x % y
  }

  def neg(x: Int): Int = {
    -x
  }

  val b: Int = 3 + 4
}