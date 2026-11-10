import stainless.annotation.*
import stainless.io.*

/** Array fields of a length fixed by a class invariant, initialised with
 *  values that are not only zeroes (see ZeroFilledFixedArrays for those):
 *  arrays of class values, and arrays of a size that is not a constant, which
 *  get the length of their field.
 */
object FixedArrayInit:

  case class Cell(values: Array[Int], count: Int):
    require(values.length == 2)

  case class Grid(cells: Array[Cell], size: Int):
    require(cells.length == 3)

  case class Board(grid: Grid, turn: Int)

  def printInit(n: Int, k: Int)(implicit @ghost state: State): Unit =
    require(n == 3)
    require(0 <= k && k <= 10)

    // An array of class values, of a constant size
    val g: Grid = Grid(Array.fill(3)(Cell(Array.fill(2)(4), 1)), 9)
    g.cells(1).values(0) = 5
    StdOut.println(g.cells(1).values(0)) // 5
    StdOut.println(g.cells(2).values(1)) // 4
    StdOut.println(g.cells(2).count) // 1
    StdOut.println(g.size) // 9

    // An array of class values, of a size that is not a constant
    val h: Grid = Grid(Array.fill(n)(Cell(Array.fill(2)(k), k + 1)), 0)
    h.cells(0).values(1) = 6
    StdOut.println(h.cells(0).values(1)) // 6
    StdOut.println(h.cells(2).values(0)) // 2
    StdOut.println(h.cells(1).count) // 3

    // An array of integers, of a size that is not a constant
    val c: Cell = Cell(Array.fill(n - 1)(8), 0)
    c.values(0) = 7
    StdOut.println(c.values(0)) // 7
    StdOut.println(c.values(1)) // 8

    // An array of zeroes, of a size that is not a constant, in a value that does not only contain zeroes
    val d: Cell = Cell(Array.fill(n - 1)(0), 5)
    StdOut.println(d.values(1)) // 0
    StdOut.println(d.count) // 5

    // An array literal of class values
    val e: Grid = Grid(Array(Cell(Array(1, 2), 3), Cell(Array(4, 5), 6), Cell(Array(7, 8), 9)), 0)
    StdOut.println(e.cells(1).values(1)) // 5
    StdOut.println(e.cells(2).count) // 9

    // A value nested in another value
    val b: Board = Board(Grid(Array.fill(n)(Cell(Array.fill(2)(1), 1)), 1), 4)
    b.grid.cells(1).values(1) = 9
    StdOut.println(b.grid.cells(1).values(1)) // 9
    StdOut.println(b.grid.cells(1).values(0)) // 1
    StdOut.println(b.turn) // 4

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printInit(3, 2)
