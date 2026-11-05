import stainless.annotation._
import stainless.lang._

object InternallyMutableEqualsTuple {
  class Memo(@internallyMutable private var calls: BigInt)

  def same(a: (BigInt, Memo), b: (BigInt, Memo)): Boolean = a == b
}
