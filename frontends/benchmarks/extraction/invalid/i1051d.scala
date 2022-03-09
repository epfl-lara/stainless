object i1051d {
  case class B(var x: Int)

  def t1: Unit = {
    val b = B(42)
    f((b, b)) // Illegal aliasing within expr
  }

  def f(bb: (B, B)): Unit = {
     val x1 = bb._1.x
     bb._2.x = 50
     assert(bb._1.x == x1)
  }
}