import stainless.lang._
import stainless.collection._

// Testing subfunction matching within subfunctions
// That is, we do not only try to match function appearing in top-level `eval` (mul and myMul)
// but also functions transitively appearing in mul and myMul
// Furthermore, Candidate mySub arguments are swapped
object Model {
  // Top level
  def eval(x: BigInt, y: BigInt): BigInt = mul(x, y)

  def mul(x: BigInt, y: BigInt): BigInt = {
    decreases(if (x <= 0) -x else x)
    if (x == 0) BigInt(0)
    else if (x > 0) add(mul(x - 1, y), y)
    else sub(mul(x + 1, y), y)
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
}