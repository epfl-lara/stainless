import stainless.annotation._
import stainless.lang._
import stainless.math.max

object ExternPost {
  def truth(i: BigInt): Boolean = true

  @extern
  def f(n: BigInt): Unit = {
  } ensuring(_ => recursive(n, truth))

  def g(n: BigInt): Unit = {
    f(n)
    assert(recursive(n, truth))
  }

  def recursive(n: BigInt, p: BigInt => Boolean): Boolean = {
    decreases(max(n,0))
    if (n <= 0) true
    else recursive(n-1,p)
  }
}
