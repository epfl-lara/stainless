// Illustrates how to introduce and specify state that is as good as unobservable for verification purposes
import stainless.lang._
import stainless.annotation._

object Cached {
  final case class Cached[K,V](f: K => V, var cache: Option[(K, V)]) {
    require(
      cache match {
        case None() => true
        case Some((k,v)) => v == f(k)
      }
    )

    def insert(k: K): V = {
      val v = f(k)
      cache = Some((k,v))
      v
    }

    @opaque
    def apply(k: K): V = {
      cache match {
        case Some((k0,v0)) =>
          if (k == k0) v0
          else insert(k)
        case None() => insert(k)
      }
   }.ensuring(_ == f(k)) // for verification purposes, cached function will work like the original one
  }
}
