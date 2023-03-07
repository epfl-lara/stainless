import stainless.lang._
import stainless.collection._

object Candidate1 {

  def dup[S, T](n: BigInt, s: S, t: T): List[(S, T)] = {
    decreases(if (n <= 0) BigInt(0) else n)
    if (n == 0) Nil()
    else if (n < 0) List((s, t), (s, t), (s, t), (s, t), (s, t)) // Ok because norm will remove this
    else (s, t) :: dup(n - 1, s, t)
  }

}