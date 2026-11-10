import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object InternallyMutablePattern {
  case class Cache(@internallyMutable private var last: BigInt, size: BigInt)

  def lastOf(c: Cache): BigInt = c match {
    case Cache(l, _) => l
  }
}
