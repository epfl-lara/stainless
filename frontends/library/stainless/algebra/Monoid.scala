package stainless
package algebra

import stainless.lang._
import stainless.annotation._

@library
trait Monoid[A] extends Semigroup[A] {

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

@library
case class Sum[A](getSum: A) extends AnyVal

@library
case class Prod[A](getProd: A) extends AnyVal

@library
object Monoid {

  @inline
  final def apply[A](implicit ev: Monoid[A]): Monoid[A] = ev
}

