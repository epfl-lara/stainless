import stainless.collection.*
import stainless.lang.*

object i1847e:
  def f[T](xs: List[T]): BigInt =
    decreases(xs.size)
    xs match
      case Nil() => BigInt(0)
      case Cons(_, t) => g(t)

  def g[T](xs: List[T]): BigInt =
    f(xs)
