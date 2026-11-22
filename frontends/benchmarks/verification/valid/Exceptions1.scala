import stainless.lang._

// Exceptions are case classes that extend stainless.lang.Exception
case class NegativeInput(x: BigInt) extends Exception
case class TooLarge(x: BigInt) extends Exception

object Exceptions1 {
  // `throwing` states which exceptions a function may throw; `ensuring` is about its normal results
  def check(x: BigInt): BigInt = {
    if (x < 0) throw NegativeInput(x)
    if (x > 100) throw TooLarge(x)
    x
  }.ensuring(res => 0 <= res && res <= 100).throwing {
    case NegativeInput(y) => y == x && x < 0
    case TooLarge(y) => y == x && x > 100
    case _ => false
  }

  def safe(x: BigInt): BigInt = {
    try {
      check(x)
    } catch {
      case NegativeInput(_) => BigInt(0)
      case TooLarge(_) => BigInt(100)
    }
  }.ensuring(res => 0 <= res && res <= 100)

  // A function without `throwing` may not let an exception escape
  def noThrow(x: BigInt): BigInt = {
    require(x >= 0 && x <= 100)
    check(x)
  }.ensuring(_ == x)

  // An exception thrown in a loop leaves the loop
  def withVars(n: BigInt): BigInt = {
    require(n >= 0)
    var i: BigInt = 0
    var acc: BigInt = 0
    try {
      (while (i < n) {
        decreases(n - i)
        acc = acc + check(i)
        i = i + 1
      }).invariant(0 <= i && i <= n && acc >= 0)
    } catch {
      case TooLarge(_) => acc = -1
      case _ => acc = -2
    }
    acc
  }.ensuring(res => res >= -2)

  def finallyRuns(x: BigInt): BigInt = {
    var count: BigInt = 0
    try {
      count = check(x)
    } catch {
      case NegativeInput(_) => count = 1
    } finally {
      count = count + 1
    }
    count
  }.ensuring(res => res >= 1).throwing {
    case TooLarge(_) => x > 100
    case _ => false
  }

  def earlyReturn(x: BigInt): BigInt = {
    try {
      if (x == 42) return BigInt(7)
      check(x)
    } catch {
      case _: NegativeInput => BigInt(-1)
      case _: TooLarge => BigInt(-2)
    }
  }.ensuring(res => res >= -2 && res <= 100)
}
