import stainless.lang._

object HigherOrderFunctionsMutableParams11 {
  
  case class A(var x: Int)

  case class FunctionWrapper(f: (A) => Int)
  case class WrapWrapper(fw: FunctionWrapper)

  def app(fw: FunctionWrapper, a: A): Int = fw match {
    case FunctionWrapper(f) => f(a)
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
