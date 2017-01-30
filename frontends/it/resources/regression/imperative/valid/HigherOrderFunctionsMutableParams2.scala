object HigherOrderFunctionsMutableParams2 {

  case class A(var x: BigInt)

  def app(f: (A) => BigInt, a: A): BigInt = {
    f(a)
  }

  def fImpl(a: A): BigInt = {
    a.x += 1
    a.x
  }


  def test(): BigInt = {
    val a = A(0)
    app(fImpl, a)
    app(fImpl, a)
    app(fImpl, a)
  } ensuring(_ == 3)

}
