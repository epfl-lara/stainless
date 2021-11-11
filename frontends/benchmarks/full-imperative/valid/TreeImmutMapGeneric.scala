import stainless.annotation.{ghost => ghostAnnot, _}
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
    @ghostAnnot def repr: Set[Cell[T]] =
      this match {
        case Leaf(data) => Set[Cell[T]](data)
        case Branch(left, right) => left.repr ++ right.repr
      }

    @ghostAnnot def valid: Boolean =
      this match {
        case Leaf(data) => true
        case Branch(left, right) =>
          (left.repr & right.repr) == Set[Cell[T]]() &&
          left.valid && right.valid
      }

    def toList: List[T] = {
      reads(repr.asRefs)
      this match {
        case Leaf(data) => List(data.value)
        case Branch(left, right) => left.toList ++ right.toList
      }
    }

    def map(f: T => T): Unit = {
      reads(repr.asRefs)
      modifies(repr.asRefs)
      require(valid)
      decreases(this)
      @ghostAnnot val oldList = toList

      this match {
        case Leaf(data) =>
          data.value = f(data.value)
          ghost { check(toList == oldList.map(f)) }

        case Branch(left, right) =>
          @ghostAnnot val (oldList1, oldList2) = (left.toList, right.toList)
          left.map(f)
          right.map(f)
          ghost { lemmaMapConcat(oldList1, oldList2, f) }; ()
      }
    } ensuring (_ => toList == old(toList.map(f)))
  }

  case class Leaf[T](data: Cell[T]) extends Tree[T]
  case class Branch[T](left: Tree[T], right: Tree[T]) extends Tree[T]
}
