import stainless.collection._

object Example {
  def tails[T] (l: List[T]) : List[List[T]] = l match {
    case Cons(_, tl) => Cons(tl, tails(tl))
    case Nil() => List(Nil())
  }
}
