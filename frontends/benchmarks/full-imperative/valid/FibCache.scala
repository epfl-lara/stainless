import stainless.lang._
import stainless.annotation._
import stainless.collection._
import stainless.lang.StaticChecks._
import stainless.proof._

object FibCacheExample {
  case class FibCache(private var cache: ListMap[BigInt, BigInt]) extends AnyHeapRef {
    private def fibPure(n: BigInt): BigInt =
      if (n <= 1) 1 else fibPure(n - 2) + fibPure(n - 1)

    def cacheProp(kv: (BigInt, BigInt)): Boolean = fibPure(kv._1) == kv._2

    def apply(n: BigInt): BigInt = {
      reads(Set(this))
      modifies(Set(this))
      require(0 <= n && cache.forall(cacheProp))
      decreases(n)
      cache.get(n) match {
        case None() =>
          val result: BigInt = if (n <= 1) 1 else apply(n - 2) + apply(n - 1)
          assert(result == fibPure(n))
          ListMapLemmas.addValidProp(cache, cacheProp, n, result)
          cache = cache + (n -> result)
          result
        case Some(result) =>
          ListMapLemmas.applyForall(cache, cacheProp, n)
          check(result == fibPure(n))
          result
      }
   }.ensuring(res => res == fibPure(n) && cache.forall(cacheProp))

    def lemmaHeapIsIrrelevant(h0: Heap, h1: Heap, n: BigInt): Unit = {
      require(
        0 <= n &&
        h0.eval { cache.forall(cacheProp) } &&
        h1.eval { cache.forall(cacheProp) }
      )
      ()
   }.ensuring(_ => h0.eval { apply(n) } == h1.eval { apply(n) })
  }
}
