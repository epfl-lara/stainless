package stainless.algebra

import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.math.Nat

@library
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

@library
object Monoid {
  case class Product[A](toProduct: A)
  case class Sum[A](toSum: A)

  // Monoid, multiplication of integers
  def multiplicationBigIntMonoid: Monoid[Product[BigInt]] = new Monoid[Product[BigInt]] {
    def identity: Product[BigInt] = Product(1)
    def combine(x: Product[BigInt], y: Product[BigInt]): Product[BigInt] = Product(x.toProduct * y.toProduct)
  }

  // Monoid, addition of integers
  def additionBigIntMonoid: Monoid[Sum[BigInt]] = new Monoid[Sum[BigInt]] {
    def identity: Sum[BigInt] = Sum(0)
    def combine(x: Sum[BigInt], y: Sum[BigInt]): Sum[BigInt] = Sum(x.toSum + y.toSum)
  }

  // Monoid, multiplication of natural numbers
  def multiplicationNatMonoid: Monoid[Product[Nat]] = new Monoid[Product[Nat]] {
    def identity: Product[Nat] = Product(Nat(1))
    def combine(x: Product[Nat], y: Product[Nat]): Product[Nat] = Product(x.toProduct * y.toProduct)
  }

  // Monoid, addition of natural numbers
  def additionNatMonoid: Monoid[Sum[Nat]] = new Monoid[Sum[Nat]] {
    def identity: Sum[Nat] = Sum(Nat(0))
    def combine(x: Sum[Nat], y: Sum[Nat]): Sum[Nat] = Sum(x.toSum + y.toSum)
  }

  // Monoid, concatenation of lists
  implicit def listConcatMonoid[T]: Monoid[List[T]] = new Monoid[List[T]] {
    def identity: List[T] = Nil[T]()
    def combine(x: List[T], y: List[T]): List[T] = x ++ y

    override def law_associativity(x: List[T], y: List[T], z: List[T]): Boolean = {
      super.law_associativity(x, y, z) because lemma_associativity(x, y, z)
    }
  }

  @induct
  private def lemma_associativity[T](x: List[T], y: List[T], z: List[T]): Boolean = {
    x ++ (y ++ z) == (x ++ y) ++ z
  }.holds

  // Monoid of options
  /* Termination doesn't work yet on this instance, if uncommented, termination checks of other instances fail as well

  implicit def optionMonoid[T](implicit ev: Semigroup[T]): Monoid[Option[T]] = new Monoid[Option[T]] {
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
  }*/
}