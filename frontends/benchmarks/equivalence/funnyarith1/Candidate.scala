import stainless.lang._
import stainless.collection._
import defs._

object Candidate {
  // Top level
  def eval(op: OpKind, x: BigInt, y: BigInt): BigInt = op match {
    case OpKind.Sub => mySub(x, y)
    case OpKind.Mul => myMul(x, y)
    case OpKind.Add => myAdd(x, y)
  }

  def myAdd(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) y
    else if (x > 0) myAdd(x - 1, y + 1)
    else myAdd(x + 1, y - 1)
  }

  def mySub(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) -y
    else if (x > 0) mySub(x - 1, y - 1)
    else mySub(x + 1, y + 1)
  }

  def myMul(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) BigInt(0)
    else if (x > 0) myAdd(myMul(x - 1, y), y)
    else mySub(myMul(x + 1, y), y)
  }
}