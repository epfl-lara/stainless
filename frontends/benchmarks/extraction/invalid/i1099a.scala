object i1099a {
  case class A(var x: Int)
  case class C(a: A)

  def f(a1: A) = {
    require(a1.x == 0)
    val a2 = a1
    // Illegal aliasing
    val c = C(a2)
    c.a.x += 1
    assert(a1.x == 0) // Incorrect, but we never pass the extraction phase anyway
  }
}
