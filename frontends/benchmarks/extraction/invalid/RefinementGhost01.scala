import language.experimental.qualifiedTypes.silent
import stainless.annotation.ghost
import stainless.lang._

case class A(@ghost val x: BigInt) {

  def f(v: BigInt): Boolean = {
    // The following refinement types should not be allowed to access ghost symbols, as its predicate is executed at runtime.
    v match {
      case _: {i: BigInt with i >= x} => true
      case _: {i: BigInt with i < x} => false
    }
  }
}