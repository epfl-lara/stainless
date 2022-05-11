import stainless.annotation._

object ImmutableClass {
  trait Immutable[@mutable T] {
    def compare(t1: T, t2: T): Boolean
  }

  case class Box(var x: BigInt)

  case object ImmutableObject extends Immutable[Box] {
    def compare(t1: Box, t2: Box): Boolean = true
  }
}