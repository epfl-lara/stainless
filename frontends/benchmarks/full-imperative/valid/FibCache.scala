import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

object FibCacheExample {
  case class FibCache(private var cache: Map[BigInt, BigInt]) extends AnyHeapRef {
    private def fibPure(n: BigInt): BigInt =
      if (n <= 1) 1 else fibPure(n - 2) + fibPure(n - 1)

    def apply(n: BigInt): BigInt = {
      reads(Set(this))
      modifies(Set(this))
      require(0 <= n && forall((m: BigInt) => cache.contains(m) ==> (cache(m) == fibPure(m))))
      decreases(n)
      cache.get(n) match {
        case None() =>
          val result: BigInt = if (n <= 1) 1 else apply(n - 2) + apply(n - 1)
          assert(result == fibPure(n))
          cache = cache + (n -> result)
          result
        case Some(result) =>
          result
      }
    } ensuring { _ => forall((m: BigInt) => cache.contains(m) ==> (cache(m) == fibPure(m))) }

    /* --- Everything up to here passes, the rest is make-believe. --- */

    // Let's pretend we have first-class heaps and a construct `at(heap)(e)` that
    // translates `e` at state `h`.
    // def lemmaHeapIsIrrelevant(h0: Heap, h1: Heap, n: BigInt): Boolean = {
    //   at(h0)(apply(n)) == at(h1)(apply(n))
    // }.holds
  }
}
