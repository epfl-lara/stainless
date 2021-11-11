import stainless.annotation.{ghost => ghostAnnot, _}
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object TreeImmutMapExample {
  // Task

  @mutable abstract class Task {
    @ghostAnnot def readSet: Set[AnyHeapRef]
    @ghostAnnot def writeSet: Set[AnyHeapRef] = { ??? : Set[AnyHeapRef] } ensuring (_.subsetOf(readSet))

    def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      ??? : Unit
    }
  }

  @inlineOnce
  def parallel(task1: Task, task2: Task): Unit = {
    reads(task1.readSet ++ task2.readSet)
    modifies(task1.writeSet ++ task2.writeSet)
    require(
      (task1.writeSet & task2.readSet).isEmpty &&
      (task2.writeSet & task1.readSet).isEmpty
    )
    task1.run()
    task2.run()
    // task1 and task2 join before this function returns
  }


  // Parallel tree map

  def lemmaMapConcat[T, R](xs: List[T], ys: List[T], f: T => R): Unit = {
    xs match {
      case Nil() =>
      case Cons(_, xs) => lemmaMapConcat(xs, ys, f)
    }
  } ensuring (_ => xs.map(f) ++ ys.map(f) == (xs ++ ys).map(f))

  case class Cell[T](var value: T) extends AnyHeapRef

  sealed abstract class Tree {
    def repr: Set[AnyHeapRef] =
      this match {
        case Leaf(_, valueCell) => Set[AnyHeapRef](valueCell)
        case Branch(left, right) => left.repr ++ right.repr
      }

    def valid: Boolean =
      this match {
        case Leaf(_, cell) => true
        case Branch(left, right) =>
          left != right &&
          (left.repr & right.repr) == Set[AnyHeapRef]() &&
          left.valid && right.valid
      }

    def toList: List[BigInt] = {
      reads(repr)
      this match {
        case Leaf(_, valueCell) => List(valueCell.value)
        case Branch(l, r) => l.toList ++ r.toList
      }
    }

    def map(f: BigInt => BigInt): Unit = {
      reads(repr)
      modifies(repr)
      require(valid)
      @ghostAnnot val oldList = toList

      this match {
        case Leaf(_, valueCell) =>
          valueCell.value = f(valueCell.value)
          ghost { check(toList == oldList.map(f)) }

        case Branch(left, right) =>
          @ghostAnnot val (oldList1, oldList2) = (left.toList, right.toList)
          left.map(f)
          right.map(f)
          ghost {
            assert(left.toList == oldList1.map(f))
            assert(right.toList == oldList2.map(f))
            lemmaMapConcat(oldList1, oldList2, f)
            assert(toList == oldList.map(f))
          }
      }
    } ensuring (_ => toList == old(toList.map(f)))

    // FIXME: Times out
/*
    def parMap(f: BigInt => BigInt): Unit = {
      reads(repr)
      modifies(repr)
      require(valid)
      @ghostAnnot val oldList = toList

      this match {
        case Leaf(_, valueCell) =>
          valueCell.value = f(valueCell.value)
          ghost { check(toList == oldList.map(f)) }

        case Branch(left, right) =>
          @ghostAnnot val (oldList1, oldList2) = (left.toList, right.toList)

          val task1 = ParMapTask(left, f)
          val task2 = ParMapTask(right, f)
          parallel(task1, task2)

          assert(left.toList == oldList1.map(f))
          assert(right.toList == oldList2.map(f))

          ghost {
            lemmaMapConcat(oldList1, oldList2, f)
            check(toList == oldList.map(f))
          }
      }
      ()
    } ensuring (_ => toList == old(toList.map(f)))
*/
  }

  case class Leaf(key: BigInt, valueCell: Cell[BigInt]) extends Tree
  case class Branch(left: Tree, right: Tree) extends Tree

/*
  // FIXME: Need to know that `tree` is `valid`!
  case class ParMapTask(tree: Tree, f: BigInt => BigInt) extends Task {
    @ghostAnnot def readSet: Set[AnyHeapRef] = tree.repr
    @ghostAnnot def writeSet: Set[AnyHeapRef] = tree.repr

    def run(): Unit = {
      reads(readSet)
      modifies(writeSet)
      tree.parMap(f)
    }
  }
*/
}
