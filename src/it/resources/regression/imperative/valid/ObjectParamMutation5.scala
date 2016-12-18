import stainless.lang._

object ObjectParamMutation5 {

  case class A(var x: Int, var y: Int)

  def swap(a: A): Unit = {
    val tmp = a.x
    a.x = a.y
    a.y = tmp
  } ensuring(_ => a.x == old(a).y && a.y == old(a).x)

  def f(): A = {
    val a = A(10, 13)
    swap(a)
    a
  } ensuring(res => res.x == 13 && res.y == 10)

}
