import stainless.lang._
import stainless.collection._

object i1405a {
  def compose(f: Int => Int, g: Int => Int) = (x: Int) => f(g(x))
  def iter(n: Int, f: Int => Int): Int => Int = {
    if (n < 0) f
    else
      n match {
        case 1 => f
        case 0 => f
        case _ =>
          val asdf = iter(n - 1, f)
          compose(f, asdf)
      }
  }
}