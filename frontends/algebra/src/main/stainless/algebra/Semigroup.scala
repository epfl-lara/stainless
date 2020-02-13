package stainless.algebra

import stainless.annotation._

@library
abstract class Semigroup[A] {
  def combine(x: A, y: A): A

  @law
  def law_associativity(x: A, y: A, z: A): Boolean = {
    combine(combine(x, y), z) == combine(x, combine(y, z))
  }
}