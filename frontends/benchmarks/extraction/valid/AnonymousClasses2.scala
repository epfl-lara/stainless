
import stainless.lang._
import stainless.collection._

object AnonymousClasses2 {

  // abstract class Monoid[M] {
  //   def empty: M
  //   def append(left: M, right: M): M
  // }

  // def testMonoid[A, B](f: (A, B) => BigInt, a: A, b: B): Monoid[BigInt] = new Monoid[BigInt] {
  //   def empty = f(a, b)
  //   def append(left: BigInt, right: BigInt): BigInt = f(a, b)
  // }

  // val bigIntAddMonoid: Monoid[BigInt] = new Monoid[BigInt] {
  //   def empty: BigInt = 0
  //   def append(left: BigInt, right: BigInt): BigInt = left + right
  // }

  // def bigIntMulMonoid: Monoid[BigInt] = {
  //   val one: BigInt = 1

  //   case class BigIntMulMonoid() extends Monoid[BigInt] {
  //     def empty: BigInt = one
  //     def append(left: BigInt, right: BigInt): BigInt = left * right
  //   }

  //   BigIntMulMonoid()
  // }

  // def listMonoid[A]: Monoid[List[A]] = new Monoid[List[A]] {
  //   def empty: List[A] = Nil()
  //   def append(left: List[A], right: List[A]): List[A] = left ++ right
  // }

  // def optionMonoid[A](aMonoid: Monoid[A]): Monoid[Option[A]] = new Monoid[Option[A]] {
  //   def empty: Option[A] = None()
  //   def append(left: Option[A], right: Option[A]): Option[A] = (left, right) match {
  //     case (Some(l), Some(r)) => Some(aMonoid.append(l, r))
  //     case _ => None()
  //   }
  // }

  // case class Box[A](value: A)

  // case class BoxMonoid[X](x: X) extends Monoid[Box[X]] {
  //   def append(left: Box[X], right: Box[X]): Box[X] = Box(x)
  // }

  // def boxMonoid1[X](x: X): Monoid[Box[X]] = new BoxMonoid[X](x)

  // def boxMonoid2[X](x: X): Monoid[Box[X]] = new Monoid[Box[X]] {
  //   def append(left: Box[X], right: Box[X]): Box[X] = Box(x)
  // }

}
