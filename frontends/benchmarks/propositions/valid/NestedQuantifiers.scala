import stainless.lang._

// Predicates that state quantifiers are values: they can be passed to the functions that
// state them, such as a user-defined existential quantifier, and be returned.
object NestedQuantifiers {
  def exists[A](p: A => Boolean): Boolean = !forall((a: A) => !p(a))

  // for all x there is a y above f(x)
  def bounded(f: BigInt => BigInt): Boolean =
    forall((x: BigInt) => exists((y: BigInt) => f(x) < y))

  // there is a y above all f(x)
  def uniformlyBounded(f: BigInt => BigInt): Boolean =
    exists((y: BigInt) => forall((x: BigInt) => f(x) < y))

  def upperBounds(f: BigInt => BigInt): BigInt => Boolean =
    (y: BigInt) => forall((x: BigInt) => f(x) < y)

  def uniformlyBounded2(f: BigInt => BigInt): Boolean = exists(upperBounds(f))
}
