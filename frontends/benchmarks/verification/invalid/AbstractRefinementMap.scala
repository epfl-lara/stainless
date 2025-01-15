import stainless.annotation._
import stainless.collection._
import stainless.lang._

object AbstractRefinementMap {

  case class ~>>[A, B](pre: A => Boolean, private val f: A => B, post: B => Boolean) {

    def apply(a: A): B = {
      require(pre(a))
      f(a)
    }.ensuring(post) // Invalid: missing a class invariant such as require(forall((x: A) => pre(x) ==> post(f(x))))
  }

  def map[A, B](l: List[A], f: A ~>> B): List[B] = {
    require(forall((x: A) => l.contains(x) ==> f.pre(x)))
    l match {
      case Cons(x, xs) => Cons[B](f(x), map(xs, f))
      case Nil() => Nil[B]()
    }
  }.ensuring { res => forall((x: B) => res.contains(x) ==> f.post(x)) }
}

