import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object LangCollection {
  final case class Ref[T](var unref: T) extends AnyHeapRef

  // no longer necessary now that require is taken into account in `reads` and `modifies`
  // def safeListLookup[T](l: List[Ref[T]], i: BigInt): Set[AnyHeapRef] = {
  //   require(0 <= i && i < l.size)
  //   Set[AnyHeapRef](l(i))
  // }

  final case class CellArray[T](content: List[Ref[T]])
  {
    def apply(i: BigInt): Unit = {
      require(0 <= i && i < content.size)
      reads(Set(content(i)))
      assert(safeListLookup(content, i) == Set(content(i)))
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
