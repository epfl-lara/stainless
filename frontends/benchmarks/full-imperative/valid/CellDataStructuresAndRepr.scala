import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object CellDataStructuresAndRepr {
  def lemmaListContainsElem[T](l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size)
    if (i > 0)
      lemmaListContainsElem(l.tail, i - 1)
    l.contains(l(i))
  }.holds

  def lemmaListNotContainsElem[T](x: T, l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size && !l.contains(x))
    if (i > 0)
      lemmaListNotContainsElem(x, l.tail, i - 1)
    l(i) != x
  }.holds

  def lemmaListNoDupNotFirst[T](l: List[T], i: BigInt): Boolean = {
    require(0 < i && i < l.size && ListOps.noDuplicate(l))
    lemmaListNotContainsElem(l(0), l.tail, i - 1)
    l(0) != l(i)
  }.holds

  def lemmaListTailElem[T](l: List[T], i: BigInt): Boolean = {
    require(0 < i && i < l.size)
    if (i > 1)
      lemmaListTailElem(l.tail, i - 1)
    l(i) == l.tail(i - 1)
  }.holds

  def lemmaListTakeElem[T](l: List[T], n: BigInt, i: BigInt): Boolean = {
    require(0 <= i && i < n && n <= l.size)
    if (i > 0)
      lemmaListTakeElem(l.tail, n - 1, i - 1)
    l.take(n)(i) == l(i)
  }.holds

  def lemmaListDropElem[T](l: List[T], n: BigInt, i: BigInt): Boolean = {
    require(0 <= n && 0 <= i && n + i < l.size)
    if (n > 0)
      lemmaListDropElem(l.tail, n - 1, i)
    l.drop(n)(i) == l(n + i)
  }.holds

  def lemmaListDropIndexOf[T](l: List[T], n: BigInt, x: T): Boolean = {
    require(0 <= n && n < l.size && ListOps.noDuplicate(l) && l.drop(n).contains(x))
    if (n > 0)
      lemmaListDropIndexOf(l.tail, n - 1, x)
    l.indexOf(x) == l.drop(n).indexOf(x) + n
  }.holds

  def lemmaListTakeIndexOf[T](l: List[T], n: BigInt, x: T): Boolean = {
    require(0 < n && n <= l.size && l.take(n).contains(x))
    if (l.head != x)
      lemmaListTakeIndexOf(l.tail, n - 1, x)
    l.indexOf(x) == l.take(n).indexOf(x)
  }.holds

  def lemmaListDropHead[T](l: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l.size)
    if (i > 0)
      lemmaListDropHead(l.tail, i - 1)
  } ensuring (_ => l(i) == l.drop(i).head)

  def lemmaListDropPlusOne[T](l: List[T], i: BigInt): Unit = {
    require(0 <= i && i < l.size)
    if (i > 0)
      lemmaListDropPlusOne(l.tail, i - 1)
  } ensuring (_ => l.drop(i + 1) == l.drop(i).tail)

  def lemmaListDropTakeConcat[T](l: List[T], from: BigInt, until: BigInt, i: BigInt): Unit = {
    require(
      0 <= from && from < until && until <= l.size &&
      0 <= i && i < until - from
    )
    // TODO:
    // l.drop(from).take(i) ++                     ++ l.drop(from + i    ).take(until - (from + i    ))   // by sublemma 1
    // l.drop(from).take(i) ++ (List(l(from + i))  ++ l.drop(from + i + 1).take(until - (from + i + 1)))  // by assoc
    // (l.drop(from).take(i) ++  List(l(from + i))) ++ l.drop(from + i + 1).take(until - (from + i + 1))   // by sublemma 2
    // l.drop(from).take(i + 1)              ++ l.drop(from + i + 1).take(until - (from + i + 1))

    // FIXME: Complete the proof of `lemmaListDropTakeConcat`.
    lemmaListDropTakeConcat(l, from, until, i)
  } ensuring { _ =>
    l.drop(from).take(i) ++ l.drop(from + i).take(until - (from + i)) ==
    l.drop(from).take(i + 1) ++ l.drop(from + i + 1).take(until - (from + i + 1))
  }


  // FIXME: Spurious counterexample when Repr is unsealed
  sealed trait Repr[@mutable T] {
    def objects(x: T): List[AnyHeapRef]

    @law
    @opaque
    def objectValidPropHolds(x: T, i: BigInt): Boolean = {
      validObjectIndex(x, i) ==> objectValidProp(x, i)
    }

    // Helpers

    @inline
    def validObjectIndex(x: T, i: BigInt): Boolean = {
      0 <= i && i < objects(x).size
    }

    def objectIndex(x: T, o: AnyHeapRef): BigInt = {
      require(objects(x).contains(o))
      objects(x).indexOf(o)
    } ensuring (_ >= 0)

    def objectValidProp(x: T, i: BigInt): Boolean = {
      require(validObjectIndex(x, i))
      lemmaListContainsElem(objects(x), i)
      objectIndex(x, objects(x)(i)) == i
    }

    def objectSet(x: T): Set[AnyHeapRef] =
      objects(x).content

    def objectIndices(x: T): List[BigInt] =
      List.range(0, objects(x).size)
  }


  /* Ref Cell */

  case class IntCell(var value: Int) extends AnyHeapRef


  /* Simple pair of cells */

  case class Pair[T](c1: IntCell, c2: IntCell) {
    require(c1 != c2)
  }

  case class PairRepr[T]() extends Repr[Pair[T]] {
    def objects(p: Pair[T]): List[AnyHeapRef] =
      List(p.c1, p.c2)

    @opaque
    override def objectValidPropHolds(p: Pair[T], i: BigInt): Boolean = {
      validObjectIndex(p, i) ==> {
        // TODO(gsps): Investigate if this needs to be sped-up / rewritten again.
        // check(lemmaListContainsElem(objects(p), i)) // Just to speed thigns up.
        assert(lemmaListContainsElem(objects(p), i))
        lemmaListContainsElem(objects(p), i)
      }
    } ensuring (_ => validObjectIndex(p, i) ==> (objectIndex(p, objects(p)(i)) == i))
  }


  /* Cell Arrays */

  case class CellArray(cells: List[IntCell]) {
    require(ListOps.noDuplicate(cells))

    @inline
    def repr: Repr[CellArray] = CellArrayRepr()

    def tail: CellArray = {
      require(cells.nonEmpty)
      CellArray(cells.tail)
    }

    def asSlice: CellArraySlice =
      CellArraySlice(this, 0, cells.size)
  }

  def upcastCells(cs: List[IntCell]): List[AnyHeapRef] = {
    cs match {
      case Nil() => Nil[AnyHeapRef]()
      case Cons(c, cs) => Cons(c, upcastCells(cs))
    }
  } ensuring (_ == cs)

  case class CellArrayRepr() extends Repr[CellArray] {
    def objects(a: CellArray): List[AnyHeapRef] = {
      upcastCells(a.cells)
    } ensuring (_ == a.cells)

    @opaque
    override def objectValidPropHolds(a: CellArray, i: BigInt): Boolean = {
      validObjectIndex(a, i) ==> {
        i > 0 ==> {
          lemmaListNoDupNotFirst(objects(a), i)
          lemmaListContainsElem(objects(a), i)
          lemmaListContainsElem(objects(a.tail), i-1)
          lemmaListTailElem(a.cells, i)
          objectValidPropHolds(a.tail, i-1)
        }
      }
    } ensuring (_ => validObjectIndex(a, i) ==> (objectIndex(a, objects(a)(i)) == i))
  }


  /* CellArraySlice */

  case class CellArraySlice(array: CellArray, from: BigInt, until: BigInt) {
    require(0 <= from && from <= until && until <= array.cells.size)

    @inline
    def repr: Repr[CellArraySlice] = CellArraySliceRepr(CellArrayRepr())

    @inline
    def size: BigInt = until - from

    @inline
    def tail: CellArraySlice = {
      require(size > 0)
      CellArraySlice(array, from + 1, until)
    }

    def slice(from: BigInt, until: BigInt): CellArraySlice = {
      require(0 <= from && from <= until && until <= this.size)
      CellArraySlice(array, this.from + from, this.from + until)
    }

    // FIXME: Complete the proof of `splitAt`'s postcondition.
    @extern
    def splitAt(i: BigInt): (CellArraySlice, CellArraySlice) = {
      require(0 <= i && i <= size)
      revealObjectSet
      (slice(0, i), slice(i, size))
    } ensuring { case (s1, s2) =>
      s1 * s2 && (s1.objectSet subsetOf objectSet) && (s2.objectSet subsetOf objectSet)
    }

    // @opaque
    // def lemmaCellValuesDistrib(cs1: List[IntCell], cs2: List[IntCell]): Unit = {
    //   reads(upcastCells(cs1).content ++ upcastCells(cs2).content)
    //   cs1 match {
    //     case Nil() => ()
    //     case Cons(c1, cs1) => lemmaCellValuesDistrib(cs1, cs2)
    //   }
    // } ensuring (_ => cellValues(cs1) ++ cellValues(cs2) == cellValues(cs1 ++ cs2))

    @opaque
    def lemmaSplitAt(i: BigInt, s1: CellArraySlice, s2: CellArraySlice): Unit = {
      reads(objectSet)
      require(0 <= i && i <= size && splitAt(i) == (s1, s2))
      // if (i == 0) {
      //   assert(s1.size == 0)
      //   assert(s1.toList == List.empty)
      //   assert(this == s2)
      //   assert(toList == s2.toList)
      //   check(toList == s1.toList ++ s2.toList)
      // } else {
      //   val s1_ = CellArraySlice(array, from, from + i - 1)
      //   val s2_ = CellArraySlice(array, from + i - 1, until)
      //   lemmaSplitAt(i - 1, s1_, s2_)
      //   lemmaListDropTakeConcat(array.cells, from, until, i - 1)
      //   assert(cells == s1.cells ++ s2.cells)
      //   assert(cells == s1_.cells ++ s2_.cells)
      //   assert(s1.cells ++ s2.cells == s1_.cells ++ s2_.cells)
      //   lemmaCellValuesDistrib(s1.cells, s2.cells)
      //   lemmaCellValuesDistrib(s1_.cells, s2_.cells)
      //   assert(cellValues(s1.cells ++ s2.cells) == cellValues(s1.cells) ++ cellValues(s2.cells))
      //   check(toList == s1.toList ++ s2.toList)
      // }

      // FIXME: Complete the proof of `lemmaSplitAt`.
      lemmaSplitAt(i, s1, s2)
      ()
    } ensuring (_ => toList == s1.toList ++ s2.toList)

    @inline
    def *(that: CellArraySlice): Boolean =
      (objectSet & that.objectSet).isEmpty


    @opaque
    def objectSet: Set[AnyHeapRef] =
      repr.objectSet(this)

    @extern
    def revealObjectSet: Unit = { () } ensuring (_ => objectSet == repr.objectSet(this))

    def validIndex(i: BigInt): Boolean = {
      val res = repr.validObjectIndex(this, i)
      revealObjectSet
      assert(res ==> lemmaValidIndexCell(cells, i))
      res
    } ensuring (res => res ==> objectSet.contains(cell(i)))

    @opaque
    private def lemmaValidIndexCell(cs: List[IntCell], i: BigInt): Boolean = {
      require(0 <= i && i < cs.size)
      if (i > 0)
        lemmaValidIndexCell(cs.tail, i - 1)
      true
    } ensuring (res => res && cs.content.contains(cs(i)))

    def cells: List[IntCell] = {
      array.cells.drop(from).take(size)
    } ensuring (_ == repr.objects(this))

    def cell(i: BigInt): IntCell = {
      require(repr.validObjectIndex(this, i))
      cells(i)
    } ensuring (_ == repr.objects(this)(i))

    def cellValues(cs: List[IntCell]): List[Int] = {
      reads(objectSet)
      require(upcastCells(cs).content subsetOf objectSet)
      cs match {
        case Nil() => Nil[Int]()
        case Cons(c, cs) => Cons(c.value, cellValues(cs))
      }
    } ensuring (_.size == cs.size)

    def toList: List[Int] = {
      reads(objectSet)
      revealObjectSet

      cellValues(cells)
    } ensuring (_.size == size)


    // Indexing (`slice(i)`)

    @opaque
    def apply(i: BigInt): Int = {
      require(validIndex(i))
      reads(objectSet)
      revealObjectSet

      lemmaApplyCell(cells, i)
      cell(i).value
    } ensuring (_ == toList(i))

    @opaque
    private def lemmaApplyCell(cs: List[IntCell], i: BigInt): Unit = {
      reads(objectSet ++ Set(cs(i)))
      require(
        0 <= i && i < cs.size &&
        upcastCells(cs).content.subsetOf(objectSet)
      )
      if (i > 0)
        lemmaApplyCell(cs.tail, i - 1)
    } ensuring (_ => cs(i).value == cellValues(cs)(i))


    // Updating (`slice(i) = v`)

    @opaque
    def update(i: BigInt, v: Int): Unit = {
      require(validIndex(i))
      reads(objectSet)
      modifies(Set(cell(i)))
      revealObjectSet

      update_(cells, 0, i, v) // effectively: `cell(i).value = v`
    } ensuring (_ => toList == old(toList).updated(i, v))

    private def update_(cs: List[IntCell], j: BigInt, i: BigInt, v: Int): Unit = {
      reads(objectSet)
      modifies(Set(cell(i)))
      require(
        validIndex(i) &&
        0 <= j && j <= size &&
        cs == cells.drop(j) && cs.size == size - j &&
        upcastCells(cs).content.subsetOf(objectSet)
      )
      val cs0 = cs
      val oldCellValues = cellValues(cs)

      cs match {
        case Nil() =>
          // The actual effect, run in the base case, so that every inductive
          //   step gets to see the same pre- and post-state.
          cell(i).value = v

        case Cons(c, cs) =>
          val oldCV = c.value

          lemmaListDropPlusOne(cells, j)
          update_(cs, j + 1, i, v) // (recursive call!)

          lemmaListDropHead(cells, j)
          assert(cells.drop(j).head == c)
          assert(c == cell(j))

          if (j == i) {
            // This is the updated cell.
            assert(c == cell(i))
            assert(c.value == v)
            check(cellValues(cs0) == oldCellValues.updated(i - j, v))
          } else {
            // This must be another, unchanged cell.
            repr.objectValidPropHolds(this, i)
            repr.objectValidPropHolds(this, j)
            assert(c != cell(i)) // by injectivity
            assert(c.value == oldCV)
            check(i - j >= 0  ==>  (cellValues(cs0) == oldCellValues.updated(i - j, v)))
            check(i - j < 0   ==>  (cellValues(cs0) == oldCellValues))
          }
          ()
      }
    } ensuring { _ =>
      cell(i).value == v &&
      cellValues(cs) == (if (i - j >= 0) old(cellValues(cs)).updated(i - j, v) else old(cellValues(cs)))
    }
  }

  case class CellArraySliceRepr(reprCAT: Repr[CellArray]) extends Repr[CellArraySlice] {
    def objects(s: CellArraySlice): List[AnyHeapRef] = {
      // reprCAT.objects(s.array).slice(s.from, s.until)
      reprCAT.objects(s.array).drop(s.from).take(s.size)
    } ensuring (_.size == s.size)

    @opaque
    override def objectValidPropHolds(s: CellArraySlice, i: BigInt): Boolean = {
      validObjectIndex(s, i) ==> {
        reprCAT.objectValidPropHolds(s.array, s.from + i)
        // --> reprCAT.objectIndex(s.array, reprCAT.objects(s.array)(s.from + i)) == s.from + i

        lemmaArrayObject(s, i)
        // --> objects(s)(i) == reprCAT.objects(s.array)(s.from + i)
        assert(objects(s)(i) == reprCAT.objects(s.array)(s.from + i))

        lemmaArrayObjectIndex(s, i)
        // --> reprCAT.objectIndex(s.array, objects(s)(i)) == objectIndex(s, objects(s)(i)) + s.from

        lemmaListContainsElem(objects(s), i)
        // assert(reprCAT.objectIndex(s.array, objects(s)(i)) == objectIndex(s, objects(s)(i)) + s.from)
        check(objectIndex(s, objects(s)(i)) == i)
        true
      }
    } ensuring (_ => validObjectIndex(s, i) ==> (objectIndex(s, objects(s)(i)) == i))

    @opaque
    def lemmaArrayObject(s: CellArraySlice, i: BigInt) = {
      require(validObjectIndex(s, i))

      val os = reprCAT.objects(s.array)
      lemmaListTakeElem(os.drop(s.from), s.size, i)
      lemmaListDropElem(os, s.from, i)
      // --> os.drop(s.from).take(s.size)(i) == os(s.from + i)
    } ensuring (_ => objects(s)(i) == reprCAT.objects(s.array)(s.from + i))

    @opaque
    def lemmaArrayObjectIndex(s: CellArraySlice, i: BigInt) = {
      require(validObjectIndex(s, i))

      val os = reprCAT.objects(s.array)
      val o = objects(s)(i)
      lemmaListContainsElem(objects(s), i)
      // --> objects(s).contains(objects(s)(i))
      lemmaListTakeIndexOf(os.drop(s.from), s.size, o)
      // --> os.drop(s.from).indexOf(o) == os.drop(s.from).take(s.size).indexOf(o)
      lemmaListDropIndexOf(os, s.from, o)
      // --> os.indexOf(o) == os.drop(s.from).take(s.size).indexOf(o) + s.from
    } ensuring (_ =>
      reprCAT.objects(s.array).indexOf(objects(s)(i)) == objects(s).indexOf(objects(s)(i)) + s.from
    )
  }


  // Example

  @opaque
  def copy(src: CellArraySlice, dst: CellArraySlice): Unit = {
    reads(src.objectSet ++ dst.objectSet)
    modifies(dst.objectSet)
    require(src.size == dst.size && src * dst)
    val oldSrcList = src.toList

    if (src.size == 1) {
      assert(dst.validIndex(0))
      assert(oldSrcList == List(src(0)))
      assert(dst.toList == List(dst(0)))

      dst(0) = src(0)

      check(dst.toList == oldSrcList)

    } else if (src.size > 1) {
      val mid = src.size / 2
      val (src1, src2) = src.splitAt(mid)
      val (dst1, dst2) = dst.splitAt(mid)

      val oldListSrc1 = src1.toList
      val oldListSrc2 = src2.toList

      copy(src1, dst1)
      assert(src1.toList == oldListSrc1)
      assert(dst1.toList == oldListSrc1)

      assert(src2.toList == oldListSrc2)

      copy(src2, dst2)
      assert(src2.toList == oldListSrc2)
      assert(dst2.toList == oldListSrc2)

      src.lemmaSplitAt(mid, src1, src2)
      assert(src.toList == src1.toList ++ src2.toList)
      dst.lemmaSplitAt(mid, dst1, dst2)
      assert(dst.toList == dst1.toList ++ dst2.toList)

      check(dst.toList == oldSrcList)

    } else {
      check(dst.toList == oldSrcList)
    }
    ()

  } ensuring (_ => dst.toList == old(src.toList))
}
