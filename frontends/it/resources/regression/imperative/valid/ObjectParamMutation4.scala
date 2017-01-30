import stainless.lang._

object ObjectParamMutation4 {

  case class A(var y: Int)

  def swapY(a1: A, a2: A): Unit = {
    val tmp = a1.y
    a1.y = a2.y
    a2.y = tmp
  } ensuring(_ => a1.y == old(a2).y && a2.y == old(a1).y)

  def f(): (Int, Int) = {
    val a1 = A(10)
    val a2 = A(10)
    a1.y = 12
    a2.y = 42
    swapY(a1, a2)
    (a1.y, a2.y)
  } ensuring(res => res._1 == 42 && res._2 == 12)

}
