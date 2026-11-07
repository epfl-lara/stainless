import stainless.annotation.*
import stainless.io.*

/** Values that only contain zeroes, of types whose arrays all have a length
 *  fixed by a class invariant. GenC zero-fills them, whatever the sizes and
 *  the elements of the arrays they are built from.
 */
object ZeroFilledFixedArrays:

  case class Cell(values: Array[Int], count: Int):
    require(values.length == 2)

  case class Grid(cells: Array[Cell], size: Int):
    require(cells.length == 3)

  case class Board(grid: Grid, turn: Int)

  def printZeroFilled(n: Int)(implicit @ghost state: State): Unit =
    require(n == 3)

    // An array of class values, of a size that is not a constant
    val g: Grid = Grid(Array.fill(n)(Cell(Array.fill(2)(0), 0)), 0)
    g.cells(1).values(0) = 5
    StdOut.println(g.cells(0).values(0)) // 0
    StdOut.println(g.cells(1).values(0)) // 5
    StdOut.println(g.cells(2).values(1)) // 0
    StdOut.println(g.cells(2).count) // 0
    StdOut.println(g.size) // 0

    // An array of class values, of a constant size
    val h: Grid = Grid(Array.fill(3)(Cell(Array.fill(2)(0), 0)), 0)
    h.cells(0).values(1) = 6
    StdOut.println(h.cells(0).values(1)) // 6
    StdOut.println(h.cells(2).values(0)) // 0

    // An array of integers, of a size that is not a constant
    val c: Cell = Cell(Array.fill(n - 1)(0), 0)
    c.values(1) = 8
    StdOut.println(c.values(0)) // 0
    StdOut.println(c.values(1)) // 8

    // A value nested in another value
    val b: Board = Board(Grid(Array.fill(n)(Cell(Array.fill(2)(0), 0)), 0), 0)
    b.grid.cells(2).values(0) = 7
    StdOut.println(b.grid.cells(2).values(0)) // 7
    StdOut.println(b.grid.cells(0).values(1)) // 0
    StdOut.println(b.turn) // 0

    // A value nested in a value that does not only contain zeroes
    val d: Board = Board(Grid(Array.fill(n)(Cell(Array.fill(2)(0), 0)), 0), 4)
    d.grid.cells(1).values(1) = 9
    StdOut.println(d.grid.cells(1).values(1)) // 9
    StdOut.println(d.grid.cells(1).values(0)) // 0
    StdOut.println(d.turn) // 4

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printZeroFilled(3)
