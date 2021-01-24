import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object ReprExample {
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
        check(lemmaListContainsElem(objects(p), i)) // Just to speed thigns up.
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

    def *(that: CellArraySlice[T]): Boolean =
      (repr.objectSet(this) & that.repr.objectSet(that)).isEmpty


/*
    // TODO: Prove validIndex, apply and update correct.

    // @inline // FIXME: Triggers assertion on malformed trees
    def objectSet: Set[AnyHeapRef] =
      repr.objectSet(this)

    @inlineOnce
    def validIndex(i: BigInt): Boolean = {
      repr.validObjectIndex(this, i)
    } ensuring (res => res ==> objectSet.contains(cell(i))) // TODO: Prove post

    @inline
    def cells: List[Cell[T]] = {
      array.cells.drop(from).take(size)
    } ensuring (_ == repr.objects(this))

    @inlineOnce
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

    def apply(i: BigInt): T = {
      require(validIndex(i))
      reads(objectSet)
      cell(i).value
    } ensuring (_ == toList(i)) // TODO: Prove post

    def xupdate(i: BigInt, v: T): Unit = {
      require(validIndex(i) && i > 0)
      reads(objectSet)
      modifies(Set(cell(i)))

      // val cells = this.cells
      // val oldVs = toList

      cell(i).value = v

      // val newVs = toList
      // assert(cell(0) != cell(i))
      // assert(newVs.head == oldVs.head)

    } ensuring (_ => toList == old(toList).updated(i, v))
*/
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
}
