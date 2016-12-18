object HigherOrderFunctionsMutableParams4 {

  case class A(var x: BigInt)

  def app(f: (A) => BigInt, a: A): BigInt = {
    f(a)
  }

  def test(): BigInt = {
    val a = A(0)
    app((a2: A) => {
      a2.x += 1
      a2.x
    }, a)
    app((a2: A) => {
      a2.x += 10
      a2.x
    }, a)
    app((a2: A) => {
      a2.x += 1
      a2.x
    }, a)
  } ensuring(_ == 12)

}
