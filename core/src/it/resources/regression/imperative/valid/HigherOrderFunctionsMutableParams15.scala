object HigherOrderFunctionsMutableParams15 {

  case class A(var x: BigInt)
  case class B(f: (A) => Unit, a: A)

  def app(b: B): Unit = {
    b.f(b.a)
  }

  def test(): BigInt = {
    val b = B((x: A) => {
      x.x = x.x + 1
    }, A(0))
    app(b)
    app(b)
    b.a.x
  } ensuring(_ == 2)

}
