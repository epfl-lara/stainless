import stainless.annotation.{indexedAt => indexedAtAnnot, _}
import stainless.lang._
import stainless.proof._

object Stream {

  case class Stream[T](head: T, tail: () => Stream[T])

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y

  def constant[T](@erasable n: BigInt, t: T): Stream[T] @indexedAtAnnot(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream(t, () => constant(n - 1, t)))
  }

  def zipWith[X, Y, Z](@erasable n: BigInt, f: (X, Y) => Z, s1: Stream[X] @indexedAtAnnot(n), s2: Stream[Y] @indexedAtAnnot(n)): Stream[Z] @indexedAtAnnot(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream(f(s1.head, s2.head), () =>
      zipWith(n - 1, f, s1.tail(), s2.tail())
    ))
  }

  def fib(@erasable n: BigInt): Stream[BigInt] @indexedAtAnnot(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream[BigInt](0, (() =>
      indexedAt(n-1, Stream[BigInt](1, (() =>
        zipWith[BigInt,BigInt,BigInt](n - 2, (a, b) => a + b, fib(n - 2), fib(n - 1).tail())
      )))
    )))
  }

  def take[T](n: BigInt, s: Stream[T] @indexedAtAnnot(n)): T = {
    require(n >= 0)
    decreases(n)
    if (n <= 0) s.head
    else take(n - 1, s.tail())
  }

  def compress(@erasable n: BigInt, s: Stream[BigInt]): Stream[BigInt] @indexedAtAnnot(n) = {
    require(n >= 0)
    decreases((n, max(9 - s.head, 0)))
    val h1: BigInt = s.head
    val h2: BigInt = s.tail().head
    if (h1 >= 1 && h1 < 9 && h2 == 1) {
      compress(n, Stream(h1 + 1, () => s.tail().tail()))
    } else {
      indexedAt(n, Stream(h1, (() => compress(n - 1, s.tail()))))
    }
  }
}
