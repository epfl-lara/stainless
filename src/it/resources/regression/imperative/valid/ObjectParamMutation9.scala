import stainless.lang._

object ObjectParamMutation9 {

  case class A(var x: Int)

  def foo(y: Int, a: A): Unit = {
    a.x = y
  }

  def update(a: A): Unit = {
    foo(10, a)
  } ensuring(_ => a.x == 10)

}
