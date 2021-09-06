import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object CellArraySimpleExample {
  final case class Ref[T](var unref: T) extends AnyHeapRef

  final case class CellArray[T](content: List[Ref[T]]) {
    def apply(i: BigInt): Unit = {
      require(0 <= i && i < content.size)
      reads(Set(content(i)))
      content(i).unref
    }

    def update(i: BigInt, v: T): Unit = {
      require(0 <= i && i < content.size)
      reads(Set(content(i)))
      modifies(Set(content(i)))
      content(i).unref = v
    }
  }
}
