import stainless.lang._
import stainless.annotation._
import scala.collection.immutable.{Set => ScalaSet}

object i1401a {
  case class Set[T](@extern @pure s: ScalaSet[T]) {
    @extern
    def apply(t: T): Boolean = s(t)

    @extern
    def subsetOf(that: Set[T]): Boolean = s.subsetOf(that.s)

    @extern
    def ++(that: Set[T]): Set[T] = {
      Set(s ++ that.s)
    }.ensuring(res => this.subsetOf(res) && that.subsetOf(res))
  }
}