import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.lang.StaticChecks._
import stainless.proof.check

object CellArrayMergeSortExample {
  def listToSet[T](l: List[T]): Set[T] =
    l match {
      case Nil() => Set[T]()
      case Cons(h, t) => listToSet(t) ++ Set(h)
    }

  def lemmaListToSetContains[T](@induct l: List[T], x: T): Boolean = {
    l.contains(x) == listToSet(l).contains(x)
  }.holds

  def lemmaListTakeAll[T](@induct l: List[T]): Boolean = {
    l.take(l.size) == l
  }.holds

  def lemmaListTakeEquals1[T](l1: List[T], l2: List[T], i: BigInt): Boolean = {
    require(
      i >= 0 && i < l1.size && l1.size == l2.size &&
      l1.take(i) == l2.take(i) && l1(i) == l2(i)
    )
    if (i > 0)
      lemmaListTakeEquals1(l1.tail, l2.tail, i - 1)
    l1.take(i + 1) == l2.take(i + 1)
  }.holds

  def lemmaListUpdatedInvPrefix[T](l: List[T], i: BigInt, v: T): Boolean = {
    require(0 <= i && i < l.size)
    if (i > 0)
      lemmaListUpdatedInvPrefix(l.tail, i - 1, v)
    l.updated(i, v).take(i) == l.take(i)
  }.holds


  final case class IntCell(var value: Int) extends AnyHeapRef

  final case class IntArray(content: List[IntCell]) {
    def validIndex(i: BigInt): Boolean =
      0 <= i && i < content.size

    @inline
    def cellAsSet(i: BigInt): Set[AnyHeapRef] = {
      require(validIndex(i))
      Set[AnyHeapRef](content(i))
    }

    def apply(i: BigInt): Int = {
      reads(cellAsSet(i))
      require(validIndex(i))
      content(i).value
    }

    def update(i: BigInt, v: Int): Unit = {
      reads(cellAsSet(i))
      modifies(cellAsSet(i))
      require(validIndex(i))
      content(i).value = v
    }

    @inline
    def asView: IntArrayView = IntArrayView(this, 0, content.size)
  }


  // TODO: Add a better way of controlling mapping between original and specialized parameters

  def allInCellSet(is: List[BigInt], iav: IntArrayView): Boolean = {
    require(is.forall(iav.validIndex(_)))
    specialize(is.forall(i => iav.cellSet.contains(iav.cell(i))))
  }

  def cellsOfIndices(is: List[BigInt], iav: IntArrayView): List[AnyHeapRef] = {
    require(is.forall(iav.validIndex(_)))
    specialize(is.map((i: BigInt) => iav.cell(i) : AnyHeapRef))
  }

  final case class IntArrayView(underlying: IntArray, from: BigInt, until: BigInt) {
    require(0 <= from && from <= until && until <= underlying.content.size)

    @inline
    def size: BigInt = until - from

    def isEmpty: Boolean = from == until

    def validIndex(i: BigInt): Boolean =
      0 <= i && i < size

    private def indicesFrom(i: BigInt): List[BigInt] = {
      require(0 <= i && i <= size)
      if (i == size) Nil[BigInt]() else Cons(i, indicesFrom(i + 1))
    } ensuring { res => res.forall(validIndex) && res.size == size - i }

    def indices: List[BigInt] = {
      indicesFrom(0)
    } ensuring { _.forall(validIndex) }

    private def indicesApplied(is: List[BigInt]): List[Int] = {
      reads(cellSet)
      require(is.forall(validIndex))
      is match {
        case Nil() => Nil[Int]()
        case Cons(i, is) =>
          lemmaCellSetContainsValidIndex(i)
          Cons(apply(i), indicesApplied(is))
      }
    } ensuring (_.size == is.size)

    def lemmaIndicesAppliedElem(i: BigInt, j: BigInt): Boolean = {
      reads(cellSet)
      require(0 <= j && j <= i && i < size)
      if (i == j) {
        true
      } else {
        lemmaIndicesAppliedElem(i, j + 1)
      }
      lemmaCellSetContainsValidIndex(i)
      apply(i) == indicesApplied(indicesFrom(j))(i - j)
    }.holds

    def lemmaToListElem(i: BigInt): Boolean = {
      reads(cellSet)
      require(validIndex(i))
      // toList(i)                  == // defn.
      // indicesApplied(indices)(i) ==
      // indices.map(apply)(i)      ==
      // apply(indices(i))          == // b/c indices(i) == i
      // apply(i)
      lemmaIndicesAppliedElem(i, 0)
      apply(i) == toList(i)
    }.holds

    def toList: List[Int] = {
      reads(cellSet)
      indicesApplied(indices)
    } ensuring (_.size == size)

    // Cell access and separation

    @inline
    def cell(i: BigInt): AnyHeapRef = {
      require(validIndex(i))
      underlying.content(from + i)
    } //ensuring { res => cellSet.contains(res) }

    // def cellIndexFrom(theCell: AnyHeapRef, i: BigInt = from): BigInt = {
    //   require(validIndex(i) && cellSet.contains(theCell))
    //   if (cell(i) == theCell) {
    //     i
    //   } else if (i + 1 < until) {
    //     cellIndexFrom(theCell, i + 1)
    //   } else {
    //     // TODO: Prove contradiction here, since `cellSet contains theCell`
    //     assert(false)
    //     ??? : BigInt
    //   }
    // } ensuring { j => validIndex(j) && cell(j) == theCell }

    @inline
    def cellAsSet(i: BigInt): Set[AnyHeapRef] = {
      require(validIndex(i))
      Set[AnyHeapRef](cell(i))
    }

    // FIXME: Leads to crash in simplifyExpr during recursive call precond check of isSortedFrom
    //@inline
    def cellSet: Set[AnyHeapRef] =
      listToSet(cellsOfIndices(indices, this))

    def *(that: IntArrayView): Boolean =
      (this.cellSet & that.cellSet).isEmpty

    def allDistinctFrom(i: BigInt, excluded: Set[AnyHeapRef]): Boolean = {
      require(0 <= i && i <= size)
      if (i == size) {
        true
      } else {
        val c = cell(i)
        !excluded.contains(c) && allDistinctFrom(i + 1, excluded ++ Set(c))
      }
    }

    def allDistinct: Boolean = allDistinctFrom(0, Set.empty)

    // def allDistinct: Boolean =
    //   indices.forall(i => cellIndexFrom(cell(i), from) == i)


    // Various lemmas

    def lemmaCellSetContainsOne(i: BigInt, start: BigInt): Boolean = {
      require(validIndex(i) && 0 <= start && start <= size && start <= i)
      if (start != i)
        lemmaCellSetContainsOne(i, start + 1)
      cellsOfIndices(indicesFrom(start), this).contains(cell(i))
    }.holds

    def lemmaCellSetContains(is: List[BigInt]): Boolean = {
      require(is.forall(validIndex))
      is match {
        case Nil() => true
        case Cons(i, is) =>
          lemmaCellSetContainsOne(i, 0)
          lemmaListToSetContains(cellsOfIndices(indices, this), cell(i))
          check(cellSet.contains(cell(i)))
          lemmaCellSetContains(is)
      }
      allInCellSet(is, this)
    }.holds

    def lemmaCellSetContainsValidIndex(i: BigInt): Boolean = {
      require(validIndex(i))
      lemmaCellSetContains(List(i))
      cellSet.contains(cell(i))
    }.holds


    // Access

    def apply(i: BigInt): Int = {
      reads(cellAsSet(i))
      require(validIndex(i))
      underlying(from + i)
    }

    def update(i: BigInt, v: Int): Unit = {
      reads(cellAsSet(i))
      modifies(cellAsSet(i))
      require(validIndex(i))
      underlying(from + i) = v
    }

    // TODO: State this as a two-state lemma about `update`
    def update2(i: BigInt, v: Int): Unit = {
      reads(cellSet)
      modifies(cellAsSet(i))
      require(validIndex(i))
      underlying(from + i) = v
    } ensuring (_ => toList == old(toList).updated(i, v))

    @inline
    def slice(from: BigInt, until: BigInt): IntArrayView = {
      require(0 <= from && from <= until && until <= size)
      IntArrayView(underlying, this.from + from, this.from + until)
    } //ensuring { res => res.cellSet subsetOf this.cellSet }


    // Copying

    def copyToFrom(that: IntArrayView, i: BigInt): Unit = {
      reads(cellSet ++ that.cellSet)
      modifies(that.cellSet)
      require(
        this * that && size == that.size && 0 <= i && i <= size &&
        toList.take(i) == that.toList.take(i)
      )
      if (i != size) {
        lemmaCellSetContainsValidIndex(i)
        that.lemmaCellSetContainsValidIndex(i)

        assert(toList.take(i) == that.toList.take(i))

        val oldThatList = that.toList

        // that(i) = this(i)
        that.update2(i, this(i))

        assert(that.toList == oldThatList.updated(i, this(i)))

        lemmaToListElem(i)
        that.lemmaToListElem(i)
        assert(that(i) == that.toList(i))
        assert(toList(i) == that.toList(i))

        lemmaListUpdatedInvPrefix(oldThatList, i, this(i))
        assert(toList.take(i) == that.toList.take(i))

        lemmaListTakeEquals1(toList, that.toList, i)
        assert(toList.take(i + 1) == that.toList.take(i + 1))

        copyToFrom(that, i + 1)
        check(toList == that.toList) // NOTE: Somehow slow (~14s)

      } else {
        lemmaListTakeAll(toList)
        lemmaListTakeAll(that.toList)
        assert(toList.take(size) == that.toList.take(size))
        check(toList == that.toList)
      }
      ()
    } ensuring (_ => toList == that.toList)

    def copyTo(that: IntArrayView): Unit = {
      reads(cellSet ++ that.cellSet)
      modifies(that.cellSet)
      require(this * that && size == that.size)
      copyToFrom(that, 0)
    } ensuring (_ => toList == that.toList)


    // Sortedness

    def isSortedFrom(i: BigInt, lowerBound: Int): Boolean = {
      reads(cellSet)
      require(0 <= i && i <= size)
      if (i < size) {
        lemmaCellSetContainsValidIndex(i)
        val vi = apply(i)
        lowerBound <= vi && isSortedFrom(i + 1, vi)
      } else {
        true
      }
    }

    def isSorted: Boolean = {
      reads(cellSet)
      isEmpty || {
        lemmaCellSetContainsValidIndex(0)
        isSortedFrom(1, apply(0))
      }
    }
  }


  // Merge sort
/*
  def merge(xs1: IntArrayView, xs2: IntArrayView,
            tmp1: IntArrayView, tmp2: IntArrayView,
            lo: BigInt, mid: BigInt, hi: BigInt,
            i: BigInt, j: BigInt, k: BigInt): Unit =
  {
    reads(xs1.cellSet ++ xs2.cellSet ++ tmp1.cellSet ++ tmp2.cellSet)
    modifies(tmp1.cellSet ++ tmp2.cellSet)
    require(
      xs1 * xs2 && xs1 * tmp1 && xs1 * tmp2 && xs2 * tmp1 && xs2 * tmp2 && tmp1 * tmp2 &&
      lo == xs1.from && xs1.from == tmp1.from &&
      xs1.until == mid && mid == xs2.from &&
      hi == xs2.until && xs2.until == tmp2.until &&
      tmp1.until == k && k == tmp2.from &&
      lo <= i && i <= mid && mid <= j && j <= hi &&
      lo <= k && k <= hi &&
      (mid - i) + (hi - j) == (hi - k) &&
      xs1.isSorted && xs2.isSorted
    )
    decreases(hi - k)

    if (k < hi) {
      assert(!tmp2.isEmpty)
      val tmp1New = IntArrayView(tmp1.underlying, tmp1.from, k + 1)
      val tmp2New = IntArrayView(tmp2.underlying, k + 1, tmp2.until)

      if (i == mid) {
        assert(j != hi)
        tmp1New(k) = xs2(j)
        merge(xs1, xs2, tmp1New, tmp2New, lo, mid, hi, i, j + 1, k + 1)
        assert(tmp1New.isSorted)
      } else if (j == hi) {
        assert(i != mid)
        tmp1New(k) = xs1(i)
        merge(xs1, xs2, tmp1New, tmp2New, lo, mid, hi, i + 1, j, k + 1)
        assert(tmp1New.isSorted)
      } else {
        val a = xs1(i)
        val b = xs2(j)
        if (a <= b) {
          tmp1New(k) = xs1(i)
          merge(xs1, xs2, tmp1New, tmp2New, lo, mid, hi, i + 1, j, k + 1)
          assert(tmp1New.isSorted)
        } else {
          tmp1New(k) = xs2(j)
          merge(xs1, xs2, tmp1New, tmp2New, lo, mid, hi, i, j + 1, k + 1)
          assert(tmp1New.isSorted)
        }
      }
    }
  } ensuring { _ => tmp1.isSorted }

  def mergeSort(xs: IntArrayView, tmp: IntArrayView, lo: BigInt, hi: BigInt): Unit = {
    reads(xs.cellSet ++ tmp.cellSet)
    modifies(xs.cellSet ++ tmp.cellSet)
    require(
      xs * tmp &&
      xs.allDistinct && tmp.allDistinct &&
      lo == xs.from && xs.from == tmp.from &&
      hi == xs.until && xs.until == tmp.until
    )
    decreases(hi - lo)
    val size = hi - lo
    assert(size >= 0)

    if (size > 2) {
      val mid = lo + (size / 2)
      val (xs1, xs2) = (xs.slice(lo, mid), xs.slice(mid, hi))
      val (tmp1, tmp2) = (tmp.slice(lo, lo), tmp.slice(lo, hi))

      mergeSort(xs, tmp, lo, mid)
      assert(xs1.isSorted)
      mergeSort(xs, tmp, mid, hi)
      assert(xs2.isSorted)

      // TODO: This currently doesn't make sense, need to start with large tmp1?
      merge(xs1, xs2, tmp1, tmp2, lo, mid, hi, lo, mid, lo)
      assert(tmp1.isSorted)

      // TODO: Implement
      // tmp.copy(xs, lo, hi)
      assert(xs.isSorted)

    } else if (size == 2) {
      val (a, b) = (xs(lo), xs(lo + 1))
      if (a > b) {
        xs(lo) = b
        xs(lo + 1) = a
      }
    }
  } ensuring { _ => xs.isSorted }
*/
}
