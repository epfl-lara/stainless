import stainless.annotation._
import stainless.lang._

object InternallyMutableEqualsNested {
  sealed trait Fun
  case class Memo(@internallyMutable private var calls: BigInt) extends Fun
  case class Plain(n: BigInt) extends Fun

  case class Wrapper(f: Fun, n: BigInt)

  def different(a: Wrapper, b: Wrapper): Boolean = a != b
}
