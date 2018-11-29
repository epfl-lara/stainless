package stainless
package algebra

import stainless.lang._
import stainless.annotation._

// @library
trait Eq[A] {

  def eqv(x: A, y: A): Boolean

  def neqv(x: A, y: A): Boolean =
    !eqv(x, y)

  @law
  def law_reflexivity(x: A): Boolean = {
    eqv(x, x)
  }

  @law
  def law_antiSymmetry(x: A, y: A): Boolean = {
    eqv(x, y) ==> eqv(y, x)
  }

  @law
  def law_transitivity(x: A, y: A, z: A): Boolean = {
    (eqv(x, y) && eqv(y, z)) ==> eqv(x, z)
  }
}

@library
object Eq {

  @inline
  final def apply[A](implicit ev: Eq[A]): Eq[A] = ev
}
