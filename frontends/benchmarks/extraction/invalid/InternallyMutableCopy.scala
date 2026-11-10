import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutableCopy {
  case class Cache(@internallyMutable private var last: BigInt, size: BigInt)

  def resize(c: Cache): Cache = c.copy(size = 3)
}
