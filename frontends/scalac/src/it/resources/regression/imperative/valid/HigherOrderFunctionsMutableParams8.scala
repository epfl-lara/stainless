import stainless.lang._

object HigherOrderFunctionsMutableParams8 {
  
  case class A(var x: Int)

  case class FunctionWrapper(f: (A) => Int)

  def app(wrap: FunctionWrapper, a: A): Int = {
    wrap.f(a)
  }

  def fImpl(a: A): Int = {
    a.x += 1
    a.x
  }

  def test(): Int = {
    val a = A(0)
    val wrap = FunctionWrapper(fImpl)
    app(wrap, a)
    app(wrap, a)
    a.x
  } ensuring(_ == 2)


}
