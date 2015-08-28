
import leon.lang._

object Composition {
  def passing_1(f: (Int) => Int, g: (Int) => Int, x: Int): Int = {
    require(g(1) == 2 && forall((a: Int) => f(g(a)) == a))
    val a = g(x)
    if(x == 1)
      f(g(a))
    else 2
  } ensuring { _ == 2 }
}

// vim: set ts=4 sw=4 et:
