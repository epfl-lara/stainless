import stainless.annotation._
import stainless.collection._
import stainless.lang._

object AbstractRefinementMap2 {
  abstract class ~>[A,B] {
    val pre: A => Boolean
    val ens: B => Boolean

    case class RefineA(x: A) {
      require(pre(x))
    }
    val f: RefineA => B 
    val transformInEns = assert(forall((x: A) => pre(x) ==> ens(f(RefineA(x)))))

    def apply(x: A): B = {
      require(pre(x))
      f(RefineA(x))
    } ensuring((y: B) => ens(y))
  }

  def map[A, B](l: List[A], f: A ~> B): List[B] = {
    require(forall((x: A) => l.contains(x) ==> f.pre(x)))
    l match {
      case Cons(x, xs) => Cons[B](f(x), map(xs, f))
      case Nil() => Nil[B]()
    }
  } ensuring { res => forall((x: B) => res.contains(x) ==> f.ens(x)) }
}
