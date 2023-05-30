package stainless.algebra

import stainless.annotation._

@library
abstract class Group[A] extends Monoid[A] {
  def inverse(x: A): A

  @law
  def law_leftInverse(x: A): Boolean = {
    combine(inverse(x), x) == identity
  }

  @law
  def law_rightInverse(x: A): Boolean = {
    combine(x, inverse(x)) == identity
  }
}