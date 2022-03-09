object i1051a {
  case class A(val left: B, val right: B)
  case class B(var x: Int)

  def t: Unit = {
    val b = B(42)
    f(A(b,b)) // Illegal aliasing within expr
  }

  def f(a: A): Unit = {
    val x1 = a.left.x
    a.right.x = 50
    assert(a.left.x == x1)
  }
}