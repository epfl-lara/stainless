package stainless
package algebra

import stainless.lang._
import stainless.annotation._

@library
trait PartialOrder[A] extends Eq[A] {

  def partialCompare(x: A, y: A): Comparison

  def eqv(x: A, y: A): Boolean = partialCompare(x, y).isEquals

  def lt(x: A, y: A): Boolean    = partialCompare(x, y).isLess
  def lteqv(x: A, y: A): Boolean = partialCompare(x, y).isLessOrEquals

  def gt(x: A, y: A): Boolean    = partialCompare(x, y).isGreater
  def gteqv(x: A, y: A): Boolean = partialCompare(x, y).isGreaterOrEquals

  @law
  override def law_reflexivity(x: A): Boolean = {
    lteqv(x, x)
  }

  @law
  override def law_antiSymmetry(x: A, y: A): Boolean = {
    ((lteqv(x, y) && lteqv(y, x)) ==> eqv(x, y))
  }

  @law
  override def law_transitivity(x: A, y: A, z: A): Boolean = {
    (lteqv(x, y) && lteqv(y, z)) ==> lteqv(x, z)
  }
}

@library
object PartialOrder {

  @inline
  final def apply[A](implicit ev: PartialOrder[A]): PartialOrder[A] = ev
}
