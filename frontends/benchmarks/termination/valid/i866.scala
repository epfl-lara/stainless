import stainless.collection.*
import stainless.lang.*

object i866:
  def some_lemma(x: Int, xs: List[Int]): Boolean =
    !the_law(xs) || the_law(xs)

  def the_law(xs: List[Int]): Boolean =
    decreases(xs.size)
    xs match
      case Nil() => true
      case Cons(x, xs) => some_lemma(x, xs)
