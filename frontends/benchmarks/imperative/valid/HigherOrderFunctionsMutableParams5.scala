object HigherOrderFunctionsMutableParams5 {

  case class A(var x: BigInt)

  def repeat(f: (A, BigInt) => Unit, n: BigInt, a: A): Unit = {
    require(n >= 0)
    if(n > 0) {
      f(a, n)
      repeat(f, n-1, a)
    }
  }

  def fImpl(a: A, n: BigInt): Unit = {
    a.x += 1
  }

  def test(): BigInt = {
    val a = A(0)
    repeat(fImpl, 3, a)
    a.x
  } ensuring(_ == 3)

}
