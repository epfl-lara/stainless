import stainless.lang._

object HigherOrderFunctionsMutableParams9 {
  
  case class A(var x: Int)

  case class FunctionWrapper(f: (A) => Int)
  case class WrapWrapper(fw: FunctionWrapper)

  def app(ww: WrapWrapper, a: A): Int = {
    ww.fw.f(a)
  }

  def fImpl(a: A): Int = {
    a.x += 1
    a.x
  }

  def test(): Int = {
    val a = A(0)
    val wrap = WrapWrapper(FunctionWrapper(fImpl))
    app(wrap, a)
    app(wrap, a)
    a.x
  } ensuring(_ == 2)

}
