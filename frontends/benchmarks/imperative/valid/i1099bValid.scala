object i1099bValid {
  case class A(var x: Int)
  case class C(a: A)

  def f(a0: A, a1: A, cond: Boolean) = {
    require(a0.x == 0 && a1.x == 1)
    val a2 = if (cond) a0 else a1
    val c = C(a2)
    c.a.x += 1
    assert(a0.x == (if (cond) 1 else 0))
    assert(a1.x == (if (cond) 1 else 2))
  }
}
