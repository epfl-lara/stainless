import stainless.lang._

object HigherOrderFunctionsMutableParams18 {

  case class A(var x: Int)
  case class F(f: (A) => Int)

  val inc = F(a => {
    a.x += 1
    a.x
  })

  def test(a: A): Int = {
    inc.f(a)
  } ensuring((res: Int) => a.x == old(a).x + 1)

}
