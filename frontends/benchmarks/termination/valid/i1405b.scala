import stainless.lang._
import stainless.collection._

object i1405b {
  def iter(n: Int, f: Int => Int): Int => Int = {
    def compose(f: Int => Int, g: Int => Int) = (x: Int) => f(g(x))
    if (n < 0) f
    else if (n == 0 || n == 1) f
    else compose(f, iter(n - 1, f))
  }
}