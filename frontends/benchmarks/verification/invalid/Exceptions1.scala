import stainless.lang._
import stainless.collection._

case class NegativeInput(x: BigInt) extends Exception
case class TooLarge(x: BigInt) extends Exception

object Exceptions1 {
  def check(x: BigInt): BigInt = {
    if (x < 0) throw NegativeInput(x)
    if (x > 100) throw TooLarge(x)
    x
  }.ensuring(res => 0 <= res && res <= 100).throwing {
    case NegativeInput(y) => y == x && x < 0
    case TooLarge(y) => y == x && x > 100
    case _ => false
  }

  def predTooStrong(x: BigInt): BigInt = {
    check(x)
  }.throwing {
    case NegativeInput(_) => true
    case _ => false
  }

  def uncaught(x: BigInt): BigInt = {
    try {
      check(x)
    } catch {
      case NegativeInput(_) => BigInt(0)
    }
  }

  def noRequire(x: BigInt): BigInt = check(x)

  def finallyWrong(x: BigInt): BigInt = {
    require(x >= 0 && x <= 100)
    var count: BigInt = 0
    try {
      count = check(x)
    } finally {
      count = count + 1
    }
    count
  }.ensuring(res => res >= 2)

  def loopWrong(n: BigInt): BigInt = {
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
    }
    acc
  }.ensuring(res => res >= 0)

  def returnWrong(x: BigInt): BigInt = {
    try {
      if (x == 42) return BigInt(7)
      check(x)
    } catch {
      case _: NegativeInput => BigInt(-1)
      case _: TooLarge => BigInt(-2)
    }
  }.ensuring(res => res != 7)

  def rethrowWrong(x: BigInt): BigInt = {
    try {
      check(x)
    } catch {
      case NegativeInput(y) => throw TooLarge(y)
    }
  }.throwing {
    case TooLarge(y) => y > 100
    case _ => false
  }

  def lambdaThrows(l: List[BigInt]): List[BigInt] = {
    l.map(x => check(x))
  }
}
