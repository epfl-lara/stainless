package stainless
package algebra

import stainless.lang._
import stainless.annotation._

trait Order[A] extends PartialOrder[A] {

  def compare(x: A, y: A): Int

  def comparison(x: A, y: A): Comparison =
    Comparison.fromInt(compare(x, y))

  override def eqv(x: A, y: A): Boolean =
    compare(x, y) == 0

  override def neqv(x: A, y: A): Boolean =
    !eqv(x, y)

  override def lteqv(x: A, y: A): Boolean =
    compare(x, y) <= 0

  override def lt(x: A, y: A): Boolean =
    compare(x, y) < 0

  override def gteqv(x: A, y: A): Boolean =
    compare(x, y) >= 0

  override def gt(x: A, y: A): Boolean =
    compare(x, y) > 0

  @law
  def law_totality(x: A, y: A): Boolean = {
    lteqv(x, y) || lteqv(y, x)
  }
}

@library
object Order {

  @inline
  final def apply[A](implicit ev: Order[A]): Order[A] = ev
}
