import stainless.lang._

object ObjectParamMutation6 {

  case class A(var x: BigInt)

  def inc(a: A): Unit = {
    a.x += 1
  } ensuring(_ => a.x == old(a).x + 1)

  def f(): BigInt = {
    val a = A(0)
    inc(a); inc(a); inc(a)
    a.x
  } ensuring(res => res == 3)

}
