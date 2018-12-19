package stainless
package algebra

import stainless.lang._
import stainless.annotation._

@library
trait Semigroup[A] {

  def append(x: A, y: A): A

  @law
  def law_associativity(x: A, y: A, z: A): Boolean = {
    append(append(x, y), z) == append(x, append(y, z))
  }
}

@library
object Semigroup {

  @inline
  final def apply[A](implicit ev: Semigroup[A]): Semigroup[A] = ev
}

