import stainless.lang._

object GenericInstanceTests {
  // Generic type tests of `Any` values, whose type parameters are passed as type codes
  class Box[V](val default: V) {
    case class Item(v: V)
  }

  def isItemOf[V](b: Box[V], e: Any): Boolean = e match {
    case b.Item(_) => true
    case _ => false
  }

  def same[V](b: Box[V], v: V): Unit = {
    assert(isItemOf(b, b.Item(v)))
  }

  // Type tests of other instantiations. When type parameters were passed as predicates `Object => Boolean`,
  // Inox applied the predicate of `V` in `isItemOf` to the lambdas of these tests, and `same` diverged.
  trait Values[V] {
    abstract class Value
    case class Const(v: V) extends Value
  }
  trait IntValues extends Values[BigInt] {
    case class Neg(e: Value) extends Value
  }
}
