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

  def indicesRange(start: BigInt, iav: IntArrayView) = {
    require(iav.from <= start)
    specialize(List.range(start, iav.until))
  } ensuring { _.forall(iav.validIndex(_)) }

  def allInCellSet(is: List[BigInt], iav: IntArrayView): Boolean = {
    require(is.forall(iav.validIndex(_)))
    specialize(is.forall(i => iav.cellSet.contains(iav.cell(i))))
  }

  def cellsOfIndices(is: List[BigInt], iav: IntArrayView): List[AnyHeapRef] = {
    require(is.forall(iav.validIndex(_)))
    specialize(is.map((i: BigInt) => iav.underlying.content(i) : AnyHeapRef))
  }

  final case class IntArrayView(underlying: IntArray, from: BigInt, until: BigInt) {
    require(0 <= from && from <= until && until <= underlying.content.size)

    def size: BigInt = underlying.content.size

    def isEmpty: Boolean = from == until

    def validIndex(i: BigInt): Boolean =
      from <= i && i < until

    def indices: List[BigInt] = {
      indicesRange(from, this)
    } ensuring { _.forall(validIndex) }


    // Cell access and separation

    @inline
    def cell(i: BigInt): AnyHeapRef = {
      require(validIndex(i))
      underlying.content(i)
    }

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
      require(from <= i && i <= until)
      if (i == until) {
        true
      } else {
        val c = cell(i)
        !excluded.contains(c) && allDistinctFrom(i + 1, excluded ++ Set(c))
      }
    }

    def allDistinct: Boolean = allDistinctFrom(from, Set.empty)


    // Various lemmas

    def lemmaCellSetContainsOne(i: BigInt, start: BigInt): Boolean = {
      require(validIndex(i) && from <= start && start <= i)
      if (start != i)
        lemmaCellSetContainsOne(i, start + 1)
      cellsOfIndices(indicesRange(start, this), this).contains(cell(i))
    }.holds

    def lemmaCellSetContains(is: List[BigInt]): Boolean = {
      require(is.forall(validIndex))
      is match {
        case Nil() => true
        case Cons(i, is) =>
          lemmaCellSetContainsOne(i, from)
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
      underlying(i)
    }

    def update(i: BigInt, v: Int): Unit = {
      reads(cellAsSet(i))
      modifies(cellAsSet(i))
      require(validIndex(i))
      underlying(i) = v
    }

    @inline
    def slice(from: BigInt, until: BigInt): IntArrayView = {
      require(this.from <= from && from <= until && until <= this.until)
      IntArrayView(underlying, from, until)
    }


    // Sortedness

    def isSortedFrom(i: BigInt, lowerBound: Int): Boolean = {
      reads(cellSet)
      require(from <= i && i <= until)
      if (i < until) {
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
        lemmaCellSetContainsValidIndex(from)
        isSortedFrom(from + 1, apply(from))
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
