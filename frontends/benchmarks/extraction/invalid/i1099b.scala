object i1099b {
  case class A(var x: Int)
  case class C(a: A)

  def f(a0: A, a1: A, cond: Boolean) = {
    require(a0.x == 0 && a1.x == 1)
    val a2 = if (cond) a0 else a1
    // Illegal aliasing
    val c = C(a2)
    c.a.x += 1
    assert(a1.x == 0) // Incorrect, but we never pass the extraction phase anyway
  }
}
