import stainless.annotation._
import stainless.lang._

object InternallyMutableEquals {
  case class Memo(@internallyMutable private var calls: BigInt)

  def same(a: Memo, b: Memo): Boolean = a == b
}
