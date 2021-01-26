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

  case class Cell[T](var value: T) extends AnyHeapRef


  /* Simple pair of cells */

  case class Pair[T](c1: Cell[T], c2: Cell[T]) {
    require(c1 != c2)
  }

  case class PairRepr[T]() extends Repr[Pair[T]] {
    def objects(p: Pair[T]): List[AnyHeapRef] =
      List(p.c1, p.c2)

    @opaque
    def objectValidPropHolds(p: Pair[T], i: BigInt): Boolean = {
      validObjectIndex(p, i) ==> {
        // TODO(gsps): Investigate if this needs to be sped-up / rewritten again.
        // check(lemmaListContainsElem(objects(p), i)) // Just to speed thigns up.
        assert(lemmaListContainsElem(objects(p), i))
        lemmaListContainsElem(objects(p), i)
      }
    } ensuring (_ => validObjectIndex(p, i) ==> (objectIndex(p, objects(p)(i)) == i))
  }


  /* Cell Arrays */

  case class CellArray[T](cells: List[Cell[T]]) {
    require(ListOps.noDuplicate(cells))

    @inline
    def repr: Repr[CellArray[T]] = CellArrayRepr()

    def tail: CellArray[T] = {
      require(cells.nonEmpty)
      CellArray(cells.tail)
    }

    def asSlice: CellArraySlice[T] =
      CellArraySlice(this, 0, cells.size)
  }

  def upcastCells[T](cs: List[Cell[T]]): List[AnyHeapRef] = {
    cs match {
      case Nil() => Nil[AnyHeapRef]()
      case Cons(c, cs) => Cons(c, upcastCells(cs))
    }
  } ensuring (_ == cs)

  case class CellArrayRepr[T]() extends Repr[CellArray[T]] {
    def objects(a: CellArray[T]): List[AnyHeapRef] = {
      upcastCells(a.cells)
    } ensuring (_ == a.cells)

    @opaque
    def objectValidPropHolds(a: CellArray[T], i: BigInt): Boolean = {
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

  case class CellArraySlice[T](array: CellArray[T], from: BigInt, until: BigInt) {
    require(0 <= from && from <= until && until <= array.cells.size)

    @inline
    def repr: Repr[CellArraySlice[T]] = CellArraySliceRepr(CellArrayRepr())

    @inline
    def size: BigInt = until - from

    @inline
    def tail: CellArraySlice[T] = {
      require(size > 0)
      CellArraySlice(array, from + 1, until)
    }

    def slice(from: BigInt, until: BigInt): CellArraySlice[T] = {
      require(0 <= from && from <= until && until <= this.size)
      CellArraySlice(array, this.from + from, this.from + until)
    }

    def splitAt(i: BigInt): (CellArraySlice[T], CellArraySlice[T]) = {
      require(0 <= i && i <= size)
      (slice(0, i), slice(i, size))
    } ensuring { case (s1, s2) =>
      s1 * s2 && (s1.objectSet subsetOf objectSet) && (s2.objectSet subsetOf objectSet)
    }

    def *(that: CellArraySlice[T]): Boolean =
      (repr.objectSet(this) & that.repr.objectSet(that)).isEmpty


    def objectSet: Set[AnyHeapRef] =
      repr.objectSet(this)

    def validIndex(i: BigInt): Boolean = {
      val res = repr.validObjectIndex(this, i)
      assert(res ==> lemmaValidIndexCell(cells, i))
      res
    } ensuring (res => res ==> objectSet.contains(cell(i)))

    @opaque
    private def lemmaValidIndexCell(cs: List[Cell[T]], i: BigInt): Boolean = {
      require(0 <= i && i < cs.size)
      if (i > 0)
        lemmaValidIndexCell(cs.tail, i - 1)
      true
    } ensuring (res => res && cs.content.contains(cs(i)))

    def cells: List[Cell[T]] = {
      array.cells.drop(from).take(size)
    } ensuring (_ == repr.objects(this))

    def cell(i: BigInt): Cell[T] = {
      require(repr.validObjectIndex(this, i))
      cells(i)
    } ensuring (_ == repr.objects(this)(i))

    def cellValues(cs: List[Cell[T]]): List[T] = {
      reads(objectSet)
      require(upcastCells(cs).content subsetOf objectSet)
      cs match {
        case Nil() => Nil[T]()
        case Cons(c, cs) => Cons(c.value, cellValues(cs))
      }
    } ensuring (_.size == cs.size)

    def toList: List[T] = {
      reads(objectSet)
      cellValues(cells)
    } ensuring (_.size == size)


    // Indexing (`slice(i)`)

    @opaque
    def apply(i: BigInt): T = {
      require(validIndex(i))
      reads(objectSet)
      lemmaApplyCell(cells, i)
      cell(i).value
    } ensuring (_ == toList(i))

    @opaque
    private def lemmaApplyCell(cs: List[Cell[T]], i: BigInt): Unit = {
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
    def update(i: BigInt, v: T): Unit = {
      require(validIndex(i))
      reads(objectSet)
      modifies(Set(cell(i)))
      update_(cells, 0, i, v) // effectively: `cell(i).value = v`
    } ensuring (_ => toList == old(toList).updated(i, v))

    private def update_(cs: List[Cell[T]], j: BigInt, i: BigInt, v: T): Unit = {
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

  case class CellArraySliceRepr[T](reprCAT: Repr[CellArray[T]]) extends Repr[CellArraySlice[T]] {
    def objects(s: CellArraySlice[T]): List[AnyHeapRef] = {
      // reprCAT.objects(s.array).slice(s.from, s.until)
      reprCAT.objects(s.array).drop(s.from).take(s.size)
    } ensuring (_.size == s.size)

    @opaque
    def objectValidPropHolds(s: CellArraySlice[T], i: BigInt): Boolean = {
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
    def lemmaArrayObject(s: CellArraySlice[T], i: BigInt) = {
      require(validObjectIndex(s, i))

      val os = reprCAT.objects(s.array)
      lemmaListTakeElem(os.drop(s.from), s.size, i)
      lemmaListDropElem(os, s.from, i)
      // --> os.drop(s.from).take(s.size)(i) == os(s.from + i)
    } ensuring (_ => objects(s)(i) == reprCAT.objects(s.array)(s.from + i))

    @opaque
    def lemmaArrayObjectIndex(s: CellArraySlice[T], i: BigInt) = {
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

  def readFirst(src: CellArraySlice[Int]): Unit = {
    reads(src.objectSet)
    require(src.size == 1)
    val vs = src.toList
    val v = src.apply(0)
    assert(vs(0) == v)
  }

  // def copy(src: CellArraySlice[Int]): Unit = {
  //   reads(src.objectSet)
  //   // modifies(src.objectSet)
  //   require(src.size == 1)
  //   // if (src.size == 1) {
  //   //   val oldList = src.toList
  //   //   src(0) = 123
  //   //   assert(src.toList == oldList.updated(0, 123))
  //   //   assert(src(0) == 123)
  //   // }
  //   val vs = src.toList
  //   val v = src.xapply(0)
  //   assert(vs(0) == v)
  // }

  // @opaque
  // def copy[T](src: CellArraySlice[T], dst: CellArraySlice[T]): Unit = {
  //   reads(src.objectSet ++ dst.objectSet)
  //   modifies(dst.objectSet)
  //   require(src.size == dst.size && src * dst)

  //   if (src.size == 1) {
  //     dst(0) = src(0)
  //     assert(src.cells.size == 1)
  //     assert(dst.cells.size == 1)
  //     val oldDstList = dst.toList
  //     val v = src(0)
  //     assert(dst(0) == v)
  //     assert(dst.toList == oldDstList.updated(0, v))
  //     assert(dst.toList == src.toList)
  //   } else if (src.size > 1) {
  //     val mid = src.size / 2
  //     val srcs = src.splitAt(mid)
  //     val dsts = dst.splitAt(mid)
  //     copy(srcs._1, dsts._1)
  //     copy(srcs._2, dsts._2)
  //     assert(dsts._1.toList == srcs._1.toList)
  //     assert(false)
  //     // assert(dst2.toList == src2.toList)
  //     // assert(dst.toList == src.toList)
  //   }
  //   ()

  // } //ensuring (_ => dst.toList == src.toList)
}
