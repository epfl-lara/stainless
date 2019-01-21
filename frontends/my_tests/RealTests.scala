object RealTests {

  def add(x: Real, y: Real): Real = {
    val a = Real(3)
    val b = Real(2, 1)
    x + y
  }

  def sub(x:Real, y: Real): Real = {
    x - y
  }

  def mul(x: Real, y: Real): Real = {
    x * y
  }

  def div(x: Real, y: Real): Real = {
    x / y
  }

  def neg(x: Real): Real = {
    -x
  }

  def less(x: Real, y: Real): Boolean = {
    x < y
  }

  def lessEq(x: Real, y: Real): Boolean = {
    x <= y
  }

  def greater(x: Real, y: Real): Boolean = {
    x > y
  }

  def greaterEq(x: Real, y: Real): Boolean = {
    x >= y
  }

  def equal(x: Real, y: Real): Boolean = {
    x == y
  }

  def associativity(x: Real, y: Real, z: Real): Boolean = {
    (x + y) + z == x + (y + z)
  }.holds
}