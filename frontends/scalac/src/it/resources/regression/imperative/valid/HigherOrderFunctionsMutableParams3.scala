object HigherOrderFunctionsMutableParams3 {

  case class A(var x: BigInt)

  def app(f: (A) => BigInt, a: A): BigInt = {
    f(a)
  }

  def fImpl1(a: A): BigInt = {
    a.x += 1
    a.x
  }
  def fImpl2(a: A): BigInt = {
    a.x += 10
    a.x
  }


  def test(): BigInt = {
    val a = A(0)
    app(fImpl1, a)
    app(fImpl2, a)
    app(fImpl1, a)
  } ensuring(_ == 12)

}
