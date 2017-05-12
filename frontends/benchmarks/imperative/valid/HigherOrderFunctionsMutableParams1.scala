object HigherOrderFunctionsMutableParams1 {

  case class A(var x: BigInt)

  def app(f: (A) => Unit, a: A): Unit = {
    f(a)
  }

  def fImpl(a: A): Unit = {
    a.x += 1
  }


  def test(): BigInt = {
    val a = A(0)
    app(fImpl, a)
    assert(a.x == 1)
    app(fImpl, a)
    assert(a.x == 2)
    app(fImpl, a)
    a.x
  } ensuring(_ == 3)

}
