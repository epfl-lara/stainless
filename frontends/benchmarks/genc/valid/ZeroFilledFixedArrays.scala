import stainless.annotation.*
import stainless.io.*

/** Values whose arrays all have a length fixed by a class invariant,
 *  initialised with zeroes only. GenC cannot build the array of cells, as its
 *  length `n` is not a constant, and zero-fills the whole values instead.
 */
object ZeroFilledFixedArrays:

  case class Cell(values: Array[Int], count: Int):
    require(values.length == 2)

  case class Grid(cells: Array[Cell], size: Int):
    require(cells.length == 3)

  case class Board(grid: Grid, turn: Int)

  def printZeroFilled(n: Int)(implicit @ghost state: State): Unit =
    require(n == 3)
    val g: Grid = Grid(Array.fill(n)(Cell(Array.fill(2)(0), 0)), 0)
    g.cells(1).values(0) = 5
    StdOut.println(g.cells(0).values(0)) // 0
    StdOut.println(g.cells(1).values(0)) // 5
    StdOut.println(g.cells(2).values(1)) // 0
    StdOut.println(g.cells(2).count) // 0
    StdOut.println(g.size) // 0
    val b: Board = Board(Grid(Array.fill(n)(Cell(Array.fill(2)(0), 0)), 0), 0)
    b.grid.cells(2).values(0) = 7
    StdOut.println(b.grid.cells(2).values(0)) // 7
    StdOut.println(b.grid.cells(0).values(1)) // 0
    StdOut.println(b.turn) // 0

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    printZeroFilled(3)
