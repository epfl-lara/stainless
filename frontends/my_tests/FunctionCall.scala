object IntFunctionCall {
  def add(x: Int, y: Int): Int = {
    x + y
  }

  def test(x: Int, y: Int): Int = {
    add(x, y);
  }
}