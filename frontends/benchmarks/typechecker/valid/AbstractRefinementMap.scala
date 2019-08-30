import stainless.annotation._
import stainless.collection._
import stainless.lang._

object AbstractRefinementMap {
  def map[A, B](l: List[A], f: A ~>> B): List[B] = {
    require(l.forall(f.pre))
    decreases(l)
    l match {
      case Cons(x, xs) => Cons[B](f(x), map(xs, f))
      case Nil() => Nil[B]()
    }
  } ensuring { res => res.forall(f.post) }
}
