import stainless.lang._

object HigherOrderFunctionsMutableParams8 {

  case class A(var x: BigInt)

  case class FunctionWrapper(f: (A) => BigInt)

  def app(wrap: FunctionWrapper, a: A): BigInt = {
    wrap.f(a)
  }

  def fImpl(a: A): BigInt = {
    a.x += 1
    a.x
  }

  def test(): BigInt = {
    val a = A(0)
    val wrap = FunctionWrapper(fImpl)
    app(wrap, a)
    app(wrap, a)
    a.x
  }.ensuring(_ == 2)


}
