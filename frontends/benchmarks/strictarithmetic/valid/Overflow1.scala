
object Overflow1 {

  def foo1(x: Int): Int = {
    require(x < 100)
    x + 1
  }

  def bab1(x: Byte): Int  = x + 1
  def bas1(x: Short): Int = x + 1
  def bal1(x: Int): Long  = x + 1L

  def foo2(x: Int): Int = {
    require(x > -100)
    x + (-1)
  }

  def bab2(x: Byte): Int  = x + (-1)
  def bas2(x: Short): Int = x + (-1)
  def bal2(x: Int): Long  = x + (-1L)

  def foo3(x: Int): Int = {
    require(x > -100)
    x - 1
  }

  def bab3(x: Byte): Int  = x - 1
  def bas3(x: Short): Int = x - 1
  def bal3(x: Int): Long  = x - 1L

  def foo4(x: Int): Int = {
    require(x < 100)
    x - (-1)
  }

  def bab4(x: Byte): Int  = x - (-1)
  def bas4(x: Short): Int = x - (-1)
  def bal4(x: Int): Long  = x - (-1L)

  def foo5(x: Int, y: Int): Int = {
    require(x < 0 && y > 0)
    x + y
  }

  def bab5(x: Byte, y: Byte): Int = x + y
  def bas5(x: Short, y: Short): Int = x + y
  def bal5(x: Int, y: Int): Long = x.toLong + y

  def foo6(x: Int, y: Int): Int = {
    require(x > 0 && y > 0)
    x - y
  }

  def foo7(x: Int): Int = {
    require(x > -100 && x < 100)
    x * 2
  }

  def bab7(x: Byte): Int = x * 2
  def bas7(x: Short): Int = x * 2
  def bal7(x: Int): Long = x.toLong * 2

  def fun7(x: Long): Long = {
    require(x > -100 && x < 100)
    x * 2
  }

  def foo8(x: Int): Int = {
    require(x > -100 && x < 100)
    x * 3
  }

  def foo10(x: Int, y: Int): Int = {
    require(x >= -10 && x <= 10 && y >= -10 && y <= 10)
    x * y
  }

  def foo11(): Int = {
    val x = 40000
    val y = 40000
    x * y
  }

  def fun11(): Long = {
    val x = 500000L
    val y = 500000L
    x * y
  }

  def foo12(x: Int): Int = {
    require(x != -2147483648) // -2^31
    -x
  }

  def fun12(x: Long): Long = {
    require(x != -9223372036854775808L) // -2^63
    -x
  }

  def foo13(x: Int, y: Int) = {
    require(y != 0 && (x != -2147483648 || y != -1))
    x / y
  }

  def fun13(x: Long, y: Long) = {
    require(y != 0 && (x != -9223372036854775808L || y != -1L))
    x / y
  }

}
