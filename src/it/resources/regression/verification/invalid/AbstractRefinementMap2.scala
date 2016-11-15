import stainless.annotation._
import stainless.collection._
import stainless.lang._

object AbstractRefinementMap2 {

  case class ~>[A,B](private val f: A => B, ens: B => Boolean) {
    require(forall((x: B) => ens.pre(x)) && forall((x: A) => f.pre(x) ==> ens(f(x))))

    lazy val pre = f.pre

    def apply(x: A): B = {
      require(f.pre(x))
      f(x)
    } ensuring(ens)
  }

  def map[A, B](l: List[A], f: A ~> B): List[B] = {
    require(forall((x:A) => l.contains(x) ==> f.pre(x)))
    l match {
      case Cons(x, xs) => Cons[B](f(x), map(xs, f))
      case Nil() => Nil[B]()
    }
  } ensuring { res => forall((x: B) => /* res.contains(x) ==> */ f.ens(x)) }
}

