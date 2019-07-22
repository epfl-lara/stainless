package stainless.algebra

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

object Monoid {
  import Semigroup._

  abstract class Monoid[A] extends Semigroup[A] {
    def identity: A

    @law
    def law_leftIdentity(x: A): Boolean = {
      combine(identity, x) == x
    }

    @law
    def law_rightIdentity(x: A): Boolean = {
      combine(x, identity) == x
    }
  }

  def multiplicationMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x * y

    def identity: BigInt = 1
  }

  @induct
  private def lemma_associativity[T](x: List[T], y: List[T], z: List[T]): Boolean = {
    x ++ (y ++ z) == (x ++ y) ++ z
  }.holds

  def listConcatMonoid[T]: Monoid[List[T]] = new Monoid[List[T]] {
    def identity: List[T] = Nil[T]()

    def combine(x: List[T], y: List[T]): List[T] = x ++ y

    override def law_associativity(x: List[T], y: List[T], z: List[T]): Boolean = {
      super.law_associativity(x, y, z) because lemma_associativity(x, y, z)
    }
  }

  def optionMonoid[T](implicit ev: Monoid[T]): Monoid[Option[T]] = new Monoid[Option[T]] {
    def identity: Option[T] = None[T]()
    def combine(x: Option[T], y: Option[T]): Option[T] = {
      (x, y) match {
        case (Some(a), Some(b)) => Some(ev.combine(a, b))
        case (Some(a), None()) => Some(a)
        case (None(), Some(b)) => Some(b)
        case (None(), None()) => None[T]()
      }
    }

    override def law_associativity(x: Option[T], y: Option[T], z: Option[T]): Boolean = {
      super.law_associativity(x, y, z) because {
        (x, y, z) match {
          case (Some(a), Some(b), Some(c)) => check(ev.law_associativity(a, b, c))
          case _ => true
        }
      }
    }
  }
}