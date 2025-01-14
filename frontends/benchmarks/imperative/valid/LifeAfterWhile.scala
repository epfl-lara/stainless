import stainless.lang._

object LifeAfterWhile {
  def f(N: BigInt): BigInt = {
    require(0 <= N)
    var i: BigInt = 0
    (while (i < N) {
      decreases(N - i)
      if (i == 42)
        return N - 200
      else
        i = i + 1
    }).invariant(0 <= i && i <= N)
    i = i - 100
    i
 }.ensuring(res => res <= N - 100)
}
