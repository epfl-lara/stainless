object Test {
  case class IntRef(var x:Int)
  def f = IntRef(42)

  def g(d1: IntRef, d2: IntRef) = {
    val x1 = d1.x
    d2.x = 33
    assert(d1.x==x1)
  }

  def mytest:Unit = {
    val c1 = f
    val c2 = c1
    g(c1, c2)
  }
}
