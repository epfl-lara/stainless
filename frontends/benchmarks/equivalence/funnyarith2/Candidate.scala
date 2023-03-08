import stainless.lang._
import stainless.collection._
import defs._

object Candidate {

  def eval(op: OpKind, x: BigInt, y: BigInt): BigInt = op match {
    case OpKind.Sub => mySub(y, x)
    case OpKind.Mul => myMul(x, y)
    case OpKind.Add => myAdd(x, y)
  }

  def myAdd(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) y
    else if (x > 0) myAdd(x - 1, y + 1)
    else myAdd(x + 1, y - 1)
  }

  // Computes y - x and not x - y
  def mySub(x: BigInt, y: BigInt): BigInt = {
    decreases(if (y <= 0) -y else y)
    if (y == 0) -x
    else if (y > 0) mySub(x - 1, y - 1)
    else mySub(x + 1, y + 1)
  }

  def myMul(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) BigInt(0)
    else if (x > 0) myAdd(myMul(x - 1, y), y)
    else mySub(y, myMul(x + 1, y))
  }
}