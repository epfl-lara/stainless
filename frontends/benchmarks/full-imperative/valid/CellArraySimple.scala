import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

object CellArraySimpleExample {
  final case class Ref[T](var unref: T) extends AnyHeapRef

  def safeListLookup[T](l: List[Ref[T]], i: BigInt): Set[AnyHeapRef] = {
    require(0 <= i && i < l.size)
    Set[AnyHeapRef](l(i))
  }

  // def upcast[T](l: List[Ref[T]]): List[AnyHeapRef] = {
  //   l match {
  //     case Nil() => Nil[AnyHeapRef]()
  //     case Cons(x, xs) => Cons[AnyHeapRef](x, upcast(xs))
  //   }
  // } ensuring (res => res.content == l.content)

  final case class CellArray[T](content: List[Ref[T]])
  {
    def xapply(i: BigInt): Unit = {
      reads(safeListLookup[T](content, i))
      require(0 <= i && i < content.size)
      assert(safeListLookup(content, i) == Set(content(i)))
      content(i).unref
    }

    def update(i: BigInt, v: T): Unit = {
      reads(safeListLookup[T](content, i))
      modifies(safeListLookup[T](content, i))
      require(0 <= i && i < content.size)
      content(i).unref = v
    }
  }
}
