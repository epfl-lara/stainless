import language.experimental.qualifiedTypes.silent
import stainless.annotation.ghost
import stainless.lang._

case class ClassWithInvariant(@ghost val x: BigInt) {

  def f(v: BigInt): Boolean = {
    v match {
      case _: {i: BigInt with i >= x} => true
      case _: {i: BigInt with i < x} => false
    }
  }
}