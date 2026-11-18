import stainless.lang._

object GenericOuterProjection {
  // The outer instance gives the type arguments of the enclosing class
  trait Generic[V] {
    abstract class Member { def value: V }
  }

  def projection(m: Generic[BigInt]#Member): BigInt = m.value
}
