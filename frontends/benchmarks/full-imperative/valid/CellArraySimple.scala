import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object CellArraySimpleExample {
  final case class Ref[T](var unref: T) extends AnyHeapRef derives CanEqual

  final case class CellArray[T](list: List[Ref[T]]) {
    def apply(i: BigInt)(using CanEqual[T, T]): Unit = {
      require(0 <= i && i < list.size)
      reads(Set(list(i)))
      list(i).unref
    }

    def update(i: BigInt, v: T)(using CanEqual[T, T]): Unit = {
      require(0 <= i && i < list.size)
      reads(Set(list(i)))
      modifies(Set(list(i)))
      list(i).unref = v
    }
  }
}
