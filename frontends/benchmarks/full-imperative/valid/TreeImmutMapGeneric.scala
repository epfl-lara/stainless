import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.lang.Option._
import stainless.lang.StaticChecks._
import stainless.proof.check

object TreeImmutMapGenericExample {
  // Parallel tree map

  def lemmaMapConcat[T, R](xs: List[T], ys: List[T], f: T => R): Unit = {
    xs match {
      case Nil() =>
      case Cons(_, xs) => lemmaMapConcat(xs, ys, f)
    }
  } ensuring (_ => xs.map(f) ++ ys.map(f) == (xs ++ ys).map(f))

  case class Cell[T](var value: T) extends AnyHeapRef

  sealed abstract class Tree[T] {
    def repr: Set[AnyHeapRef] =
      this match {
        case Leaf(valueCell) => Set[AnyHeapRef](valueCell)
        case Branch(left, right) => left.repr ++ right.repr
      }

    def valid: Boolean =
      this match {
        case Leaf(cell) => true
        case Branch(left, right) =>
          left != right &&
          (left.repr & right.repr) == Set[AnyHeapRef]() &&
          left.valid && right.valid
      }

    def toList: List[T] = {
      reads(repr)
      this match {
        case Leaf(valueCell) => List(valueCell.value)
        case Branch(l, r) => l.toList ++ r.toList
      }
    }

    def map(f: T => T): Unit = {
      reads(repr)
      modifies(repr)
      require(valid)
      @ghost val oldList = toList

      this match {
        case Leaf(valueCell) =>
          valueCell.value = f(valueCell.value)
          ghost { check(toList == oldList.map(f)) }

        case Branch(left, right) =>
          @ghost val (oldList1, oldList2) = (left.toList, right.toList)
          left.map(f)
          right.map(f)

          ghost {
            lemmaMapConcat(oldList1, oldList2, f)
            check(toList == oldList.map(f))
          }
      }
    } ensuring (_ => toList == old(toList.map(f)))
  }

  case class Leaf[T](valueCell: Cell[T]) extends Tree[T]
  case class Branch[T](left: Tree[T], right: Tree[T]) extends Tree[T]
}
