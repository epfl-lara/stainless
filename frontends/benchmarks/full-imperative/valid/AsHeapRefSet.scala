import stainless.lang._
import stainless.annotation._
import stainless.collection._

// Set[T <: AnyHeapRef]#asRefs is convenient for specifying reads and modifies clauses
object AsHeapRefSetExample {
  case class Cell(var value: BigInt) extends AnyHeapRef

  def increasing(cells: List[Cell], bound: BigInt = 0): Boolean = {
    reads(cells.content.asRefs)
    cells match {
      case Nil() => true
      case Cons(cell, cells0) => cell.value >= bound && increasing(cells0, cell.value)
    }
  }

  def combine(cells1: List[Cell], cells2: List[Cell]): Unit = {
    reads(cells1.content.asRefs ++ cells2.content.asRefs)
    require(
      cells1.nonEmpty && cells2.nonEmpty &&
      cells1.last.value <= cells2.head.value &&
      increasing(cells1) && increasing(cells2)
    )
    ()
  }
}
