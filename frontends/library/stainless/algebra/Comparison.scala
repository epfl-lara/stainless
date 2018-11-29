package stainless
package algebra

import stainless.lang._
import stainless.annotation._

@library
sealed abstract class Comparison {
  val isLess: Boolean
  val isEquals: Boolean
  val isGreater: Boolean
  val isUnrelated: Boolean

  val isLessOrEquals: Boolean    = isLess    || isEquals
  val isGreaterOrEquals: Boolean = isGreater || isEquals
}

@library
object Comparison {
  def fromInt(n: Int): Comparison = {
    if (n < 0) Less
    else if (n == 0) Equals
    else Greater
  }

  @library
  final case object Less extends Comparison {
    val isLess: Boolean      = true
    val isEquals: Boolean    = false
    val isGreater: Boolean   = false
    val isUnrelated: Boolean = false
  }

  @library
  final case object Equals extends Comparison {
    val isLess: Boolean      = false
    val isEquals: Boolean    = true
    val isGreater: Boolean   = false
    val isUnrelated: Boolean = false
  }

  @library
  final case object Greater extends Comparison {
    val isLess: Boolean      = false
    val isEquals: Boolean    = false
    val isGreater: Boolean   = true
    val isUnrelated: Boolean = false
  }

  @library
  final case object Unrelated extends Comparison {
    val isLess: Boolean      = false
    val isEquals: Boolean    = false
    val isGreater: Boolean   = false
    val isUnrelated: Boolean = true
  }
}
