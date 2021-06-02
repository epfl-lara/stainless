import stainless.annotation._

object IllegalAliasing {
  case class Mut[@mutable T](var t: T)
  case class S(var s: Int)

  def f2() = {
    val a = S(1)
    val b = Mut(a)
    b.t.s = 100
    assert(a.s == 100)
  }
}
