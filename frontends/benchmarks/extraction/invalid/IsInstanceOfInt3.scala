package asInstanceOfInt3

object A {
  def test[T](x: Any, default: T): T = {
    if x.isInstanceOf[T]
    then x.asInstanceOf[T]
    else default
  }

  def testInt(x: Any): Int = test[Int](x, 0) + 0
  def testInt2: Int = test[Int](2, 0) + 0
}