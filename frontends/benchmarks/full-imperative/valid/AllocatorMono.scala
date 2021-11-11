import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.lang.StaticChecks._

object AllocatorMonoExample {
  case class Box(var v: BigInt) extends AnyHeapRef

  // >> Lemmas
  def decreasingIds(is: List[BigInt], from: BigInt): Boolean =
    is match {
      case Nil() => true
      case Cons(i, is) => from > i && decreasingIds(is, i)
    }

  def lemmaDecreasingExcludes(@induct is: List[BigInt], b1: BigInt, b2: BigInt): Unit = {
    require(decreasingIds(is, b1) && b1 <= b2)
  } ensuring (_ => !is.contains(b2))

  def increasingIds(is: List[BigInt], from: BigInt): Boolean =
    is match {
      case Nil() => true
      case Cons(i, is) => from <= i && increasingIds(is, i + 1)
    }

  def lemmaIncreasingExcludes(@induct is: List[BigInt], b1: BigInt, b2: BigInt): Unit = {
    require(increasingIds(is, b1) && b1 > b2)
  } ensuring (_ => !is.contains(b2))

  def lemmaIdContainsInjectivity(@induct bs: List[Box], b0: Box): Unit = {
    ()
  } ensuring (_ => bs.contains(b0) == bs.map(objectId).contains(objectId(b0)))
  // << Lemmas

  case class BoxAllocator(
    @ghostAnnot var bound: BigInt,
    var alloc: List[Box],
    var free: List[Box]
  ) extends AnyHeapRef {
    @ghostAnnot
    def valid: Boolean = {
      reads(Set(this))
      decreasingIds(alloc.map(objectId), bound) &&
      increasingIds(free.map(objectId), bound)
    }

    // FIXME: Figure out why this fails with @extern (add missing case in ChooseInjector & more)
    @opaque
    def apply(): Option[Box] = {
      reads(Set(this))
      modifies(Set(this))
      require(valid)

      if (free.nonEmpty) {
        @ghostAnnot val oldBound = bound
        val oldAlloc = alloc

        val o = free.head
        bound = objectId(o) + 1
        free = free.tail
        alloc = Cons(o, alloc)

        ghost {
          assert(increasingIds(free.map(objectId), objectId(o) + 1)) // from valid
          lemmaIncreasingExcludes(free.map(objectId), objectId(o) + 1, objectId(o))
          assert(!free.map(objectId).contains(objectId(o)))

          lemmaIdContainsInjectivity(free, o)
          assert(!free.contains(o))

          assert(decreasingIds(oldAlloc.map(objectId), oldBound)) // from valid
          lemmaDecreasingExcludes(oldAlloc.map(objectId), oldBound, objectId(o))
          assert(!oldAlloc.map(objectId).contains(objectId(o)))

          lemmaIdContainsInjectivity(oldAlloc, o)
          assert(!oldAlloc.contains(o))
        }

        Some[Box](o)

      } else {
        None[Box]()
      }
    } ensuring {
      case None() => valid && alloc == old(alloc)
      case Some(o) => valid && alloc == o :: old(alloc) &&
        old(!alloc.contains(o) && free.contains(o)) &&
        alloc.contains(o) && !free.contains(o)
    }
  }

  // // TODO: How do I read or modify fresh objects?
  // def sameLenFreshBoxList(ator: BoxAllocator, xs: List[Box]): Option[List[Box]] = {
  //   reads(Set(ator))
  //   modifies(Set(ator))
  //   require(ator.valid && (xs.content subsetOf ator.alloc.content))
  //   val oldContent = ator.alloc.content
  //   (xs match {
  //     case Nil() => Some(Nil[Box]())
  //     case Cons(x, xs_) =>
  //       ator() match {
  //         case None() => None()
  //         case Some(y) =>
  //           sameLenFreshBoxList(ator, xs_) match {
  //             case None() => None()
  //             // case Some(ys) => Some(Cons(y, ys))
  //             case Some(ys) =>
  //               val res = Cons(y, ys)
  //               assert(res.size == xs.size)
  //               assert(!oldContent.contains(y))
  //               assert((ys.content & oldContent).isEmpty)
  //               // assert((res.content & oldContent).isEmpty)
  //               Some(res)
  //           }
  //       }
  //   }) : Option[List[Box]]
  // } ensuring {
  //   case None() => true
  //   case Some(res) => res.size == xs.size && (res.content & old(ator.alloc.content)).isEmpty
  // }

  // def clash(ator: BoxAllocator, c: Boolean): Unit = {
  //   reads(Set(ator))
  //   modifies(Set(ator))
  //   val b: Box = if (c) ator[BoolBox].get else ator[BigIntBox].get
  //   assert(false)
  // }
}
