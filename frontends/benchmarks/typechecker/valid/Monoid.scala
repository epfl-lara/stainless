import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Monoid {

  abstract class Monoid[A] {
    def empty: A
    def append(x: A, y: A): A
  }

  case object BigIntAdditiveMonoid extends Monoid[BigInt] {
    override def empty: BigInt = 0
    override def append(x: BigInt, y: BigInt): BigInt = x + y
  }

  def sum(xs: List[BigInt]): BigInt = {
    decreases(xs)
    xs match {
      case Nil() => BigInt(0)
      case Cons(y, ys) => y + sum(ys)
    }
  }

  def foldMap[A, M](xs: List[A])(f: A => M)(implicit M: Monoid[M]): M = {
    decreases(xs)
    xs match {
      case Nil() => M.empty
      case Cons(y, ys) => M.append(f(y), foldMap(ys)(f))
    }
  }

  def test(@induct xs: List[BigInt]) = {
    sum(xs) == foldMap(xs)(x => x)(BigIntAdditiveMonoid)
  }.holds
}
