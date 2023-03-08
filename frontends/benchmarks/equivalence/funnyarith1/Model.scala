import stainless.lang._
import stainless.collection._
import defs._

// Testing subfns matching
// In Candidate.eval, the order of patmat over op is not the same here to ensure
// a different starting matching strategy from the correct one: add <-> myAdd; sub <-> mySub; mul <-> myMul
object Model {
  // Top level
  def eval(op: OpKind, x: BigInt, y: BigInt): BigInt = op match {
    case OpKind.Add => add(x, y)
    case OpKind.Sub => sub(x, y)
    case OpKind.Mul => mul(x, y)
  }

  def add(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) y
    else if (x > 0) add(x - 1, y + 1)
    else add(x + 1, y - 1)
  }

  def sub(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) -y
    else if (x > 0) sub(x - 1, y - 1)
    else sub(x + 1, y + 1)
  }

  def mul(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) BigInt(0)
    else if (x > 0) add(mul(x - 1, y), y)
    else sub(mul(x + 1, y), y)
  }
}