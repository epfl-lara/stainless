import stainless.lang._

object ObjectParamMutation1 {

  case class A(var y: Int)

  def update(a: A): Int = {
    a.y = 12
    a.y
  } ensuring(res => res == 12)

  def f(): Int = {
    val a = A(10)
    update(a)
    a.y
  } ensuring(res => res == 12)

}
