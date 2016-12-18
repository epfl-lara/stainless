import stainless.lang._

object ObjectParamMutation8 {

  case class A[B](var y: B)

  def update[B](a: A[B], b: B): B = {
    a.y = b
    a.y
  } ensuring(res => res == b)

  def f(): Int = {
    val a = A(10)
    update(a, 12)
    a.y
  } ensuring(res => res == 12)

}
