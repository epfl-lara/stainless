import stainless.annotation._

object SimpleAliasing {
  case class A(var x: Int)
  case class B(a: A)

  def f(b: B): Unit = {
    require(0 <= b.a.x && b.a.x <= 100)
    b.a.x += 1
  }

  def g(a: A): Unit = {
    require(0 <= a.x && a.x <= 100)
    val b = B(a)
    f(b)
  }
}
