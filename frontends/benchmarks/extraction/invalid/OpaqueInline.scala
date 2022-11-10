import stainless._
import stainless.lang._
import stainless.annotation._

object OpaqueInline {
  @opaque @inline // Inline with opaque forbidden, must use @inlineOnce
  def f(x: BigInt): Unit = ()
}
