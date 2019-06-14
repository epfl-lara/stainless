case class A(var x: BigInt)
case class B(var a: A)

object BadAliasing2 {
  def f(b: B) {
    val a = b.a
    a.x += 1
    assert(a == b.a)
  }
}
