object BooleanTest {
  def and(x: Boolean, y: Boolean): Boolean = {
    x && y
  }

  def or(x: Boolean, y: Boolean): Boolean = {
    x || y
  }

  def eq(x: Boolean, y: Boolean): Boolean = {
    x == y
  }

  def neg(x: Boolean) : Boolean = {
    !x
  }

  def implication(x: Boolean, y: Boolean): Boolean = {
    x ==> y
  }
}