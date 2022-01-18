import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._

// A slightly better model of an allocator that elides its implementation and is polymorphic.
object AllocatorPolyAbstractExample {
  case class Box(var v: BigInt) extends AnyHeapRef

  case class Allocator[T <: AnyHeapRef](
    @ghost var bound: BigInt,
    var alloc: List[T],
    var free: List[T]
  ) extends AnyHeapRef {
    @ghost
    def evolved(from: Heap): Boolean = {
      reads(Set(this))
      (          free.content   subsetOf from.eval(free.content )) &&
      (from.eval(alloc.content) subsetOf           alloc.content )
    }

    // Set that is practically needed to allocate and initialize new objects.
    @ghost
    def access: Set[AnyHeapRef] = {
      reads(Set(this))
      free.content.asRefs + this
    }

    // FIXME(gsps): Figure out why this fails with @extern (add missing case in ChooseInjector & more)
    @extern
    def apply(): T = {
      reads(Set(this))
      modifies(Set(this))
      ??? : T
    } ensuring { o => evolved(old(Heap.get)) &&
      old(!alloc.contains(o) && free.contains(o)) && alloc.contains(o) && !free.contains(o)
    }
  }

  def freshList(ator: Allocator[Box], xs: List[Box], v: BigInt): List[Box] = {
    reads(ator.access)
    modifies(ator.access)
    require(xs.content subsetOf ator.alloc.content)
    xs match {
      case Nil() => Nil[Box]()
      case Cons(x, xs_) =>
        val b = ator()
        b.v = v
        Cons(b, freshList(ator, xs_, v))
    }
  } ensuring { res =>
    res.size == xs.size && (res.content & old(ator.alloc.content)).isEmpty
  }
}
