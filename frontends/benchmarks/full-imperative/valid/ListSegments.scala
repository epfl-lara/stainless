import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.collection.List._
import stainless.proof._

object ListSegments {
  final case class Node[T](var value: T,
                           var next: Option[Node[T]]) extends AnyHeapRef

  def toRefs[T](list: List[Node[T]]): Set[AnyHeapRef] = {
    decreases(list.size)
    list match {
      case Nil() => Set[AnyHeapRef]()
      case Cons(x, xs) => toRefs(xs) ++ Set(x)
    }
  }
  
  // list segment that may start or end with None
  def listSeg[T](from: Option[Node[T]], to: Option[Node[T]], between: List[Node[T]]): Boolean = {
    reads(toRefs(between))
    decreases(between.size)
  
    between match {
      case Nil() => from == to
      case Cons(h, betweenRest) => from == Some[Node[T]](h) && listSeg(h.next, to, betweenRest)
    }
  }

  def join[T](a: Node[T], ab: List[Node[T]], b: Node[T], bc: List[Node[T]], c: Option[Node[T]]): Unit = {
    reads(toRefs(ab) ++ toRefs(bc))
    require(listSeg[T](Some[Node[T]](a), Some[Node[T]](b), ab) &&
            listSeg[T](Some[Node[T]](b), c, bc) &&
            (toRefs[T](ab) & toRefs[T](bc)) == Set.empty[AnyHeapRef])
  } ensuring(_ => listSeg[T](Some(a), c, ab ++ bc))
}
