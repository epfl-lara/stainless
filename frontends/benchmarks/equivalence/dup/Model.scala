import stainless.lang._
import stainless.collection._

object Model {

  def dup[S, T](n: BigInt, s: S, t: T): List[(S, T)] = {
    decreases(if (n <= 0) BigInt(0) else n)
    if (n <= 0) Nil()
    else (s, t) :: dup(n - 1, s, t)
  }

  def norm[S, T](n: BigInt, s: S, t: T, res: List[(S, T)]): List[(S, T)] = {
    if (n < 0) Nil()
    else res
  }
}