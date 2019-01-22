object Int2Arithmetic {

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

  def shiftLeft(x: Int): Int = {
    x << 2
  }

  def arithmeticShiftLeft(x: Int): Int = {
    x >> 5
  }

  def logicalShiftRight(x: Int): Int = {
    x >>> 4
  }
}