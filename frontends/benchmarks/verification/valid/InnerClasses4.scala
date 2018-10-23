import stainless.lang._
import stainless.proof._
import stainless.collection._
import stainless.annotation._

object InnerClasses4 {

  abstract class Semigroup[A] {
    def append(l: A, r: A): A

    @law
    def law_associativity(x: A, y: A, z: A): Boolean = {
      append(append(x, y), z) == append(x, append(y, z))
    }
  }

  abstract class Monoid[A] extends Semigroup[A] {
    def empty: A

    @law
    def law_leftIdentity(x: A): Boolean = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: A): Boolean = {
      append(x, empty) == x
    }
  }

  @induct
  def listAppendIsAssociative[A](x: List[A], y: List[A], z: List[A]): Boolean = {
    (x ++ y) ++ z == x ++ (y ++ z)
  }.holds

  implicit def listMonoid[A](implicit ev: Monoid[A]): Monoid[List[A]] = new Monoid[List[A]] {
    def empty: List[A] = Nil()
    def append(l: List[A], r: List[A]) = l ++ r

    override def law_associativity(x: List[A], y: List[A], z: List[A]): Boolean = {
      super.law_associativity(x, y, z) because listAppendIsAssociative(x, y, z)
    }
  }

  case class Sum(get: BigInt)
  object Sum {
    implicit def sumMonoid: Monoid[Sum] = new Monoid[Sum] {
      def empty: Sum = Sum(0)
      def append(a: Sum, b: Sum): Sum = Sum(a.get + b.get)
    }
  }

  case class Prod(get: BigInt)
  object Prod {
    implicit def prodMonoid: Monoid[Prod] = new Monoid[Prod] {
      def empty: Prod = Prod(1)
      def append(a: Prod, b: Prod): Prod = Prod(a.get * b.get)
    }
  }

  def foldMap[A, M](xs: List[A])(f: A => M)(implicit ev: Monoid[M]): M = xs match {
    case Nil() => ev.empty
    case Cons(y, ys) => ev.append(f(y), foldMap(ys)(f))
  }

}
