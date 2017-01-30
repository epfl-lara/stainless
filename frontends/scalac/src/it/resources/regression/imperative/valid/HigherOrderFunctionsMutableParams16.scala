object HigherOrderFunctionsMutableParams16 {

  case class A(var x: BigInt)
  case class B(a: A)

  def app(f: (A) => Unit, b: B): Unit = {
    f(b.a)
  }

  def test(): BigInt = {
    val f: (A => Unit) = ((x: A) => {
      x.x = x.x + 1
    })
    val b = B(A(0))
    app(f, b)
    app(f, b)
    b.a.x
  } ensuring(_ == 2)

}
