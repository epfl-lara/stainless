import stainless.annotation._
import stainless.lang._
import stainless.proof._

object Stream {

  case class Stream[T](head: T, tail: () => Stream[T])

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y

  def constant[T](@erasable n: BigInt, t: T): Stream[T] @indexedAt(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream(t, () => constant(n - 1, t)))
  }

  def zipWith[X, Y, Z](@erasable n: BigInt, f: (X, Y) => Z, s1: Stream[X] @indexedAt(n), s2: Stream[Y] @indexedAt(n)): Stream[Z] @indexedAt(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream(f(s1.head, s2.head), () =>
      zipWith(n - 1, f, s1.tail(), s2.tail())
    ))
  }

  def fib(@erasable n: BigInt): Stream[BigInt] @indexedAt(n) = {
    require(n >= 0)
    decreases(n)
    indexedAt(n, Stream[BigInt](0, (() =>
      indexedAt(n-1, Stream[BigInt](1, (() =>
        zipWith[BigInt,BigInt,BigInt](n - 2, (a, b) => a + b, fib(n - 2), fib(n - 1).tail())
      )))
    )))
  }

  def take[T](n: BigInt, s: Stream[T] @indexedAt(n)): T = {
    require(n >= 0)
    decreases(n)
    if (n <= 0) s.head
    else take(n - 1, s.tail())
  }

  def compress(@erasable n: BigInt, s: Stream[BigInt]): Stream[BigInt] @indexedAt(n) = {
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

  // FIXME: need pi-types and refinement types
  // def compressOnes(
  //   n: BigInt,
  //   s: Stream[BigInt],
  //   p: (i: { i: BigInt => i > BigInt(0) }) => { u: Unit => take(i, s) == BigInt(1) }
  // ): Unit = {
  //   require(s.head >= 1 && s.head <= 9 && n >= 0)
  //   decreases((n, max(9 - s.head, 0)))
  //   val h1: BigInt = s.head
  //   val h2: BigInt = s.tail().head
  //   if (h1 >= 1 && h1 < 9 && h2 == 1) {
  //     compressOnes(n, Stream[BigInt](h1 + 1, () => s.tail().tail()), (i: { i: BigInt => (i > BigInt(0)) }) => {
  //       val p1: { u: Unit => (take[BigInt](i + BigInt(1), s) == 1) } = p((i + BigInt(1)))
  //       // val u: { u: Unit => (take[BigInt](i + BigInt(1), s) == 1) } = 
  //       check(take[BigInt](i + BigInt(1), s) == 1)
  //       // val u: { u: Unit => (take[BigInt](i, s.tail()) == 1) } = 
  //       check(take[BigInt](i, s.tail()) == 1)
  //       ()
  //     })
  //   } else {
  //     val p1: { u: Unit => (take[BigInt](BigInt(1), s) == 1) } = p(1)
  //     if (n == 0) {
  //       ()
  //     } else {
  //       compressOnes(n - 1, s.tail(), (i: { i: BigInt => (i > BigInt(0)) }) => {
  //         val p1: { u: Unit => (take[BigInt](i + BigInt(1), s) == 1) } = p((i + BigInt(1)))
  //         // val u: { u: Unit => (take[BigInt](i + BigInt(1), s) == 1) } =
  //         check(take[BigInt](i + BigInt(1), s) == 1)
  //         // val u: { u: Unit => (take[BigInt](i, s.tail()) == 1) } =
  //         check(take[BigInt](i, s.tail()) == 1)
  //         ()
  //       })
  //     }
  //   }
  // }
}
