import language.experimental.qualifiedTypes.silent
import stainless.annotation.ghost
import stainless.lang._

case class ClassWithInvariant(var x: BigInt) {
  
  @ghost
  def valid: Boolean = x >= 0

  def f(v: {v: BigInt with valid && v >= 0}): {res: BigInt with valid} = x + v
}