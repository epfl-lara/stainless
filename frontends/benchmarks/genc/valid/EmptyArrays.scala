import stainless.annotation._
import stainless.lang._
import stainless.io._

/**
 * Empty arrays in GenC. C forbids zero-length arrays, so an empty array has no buffer: its
 * `data` pointer is `NULL` and its length is 0. Covers empty array literals and `Array.fill(0)`,
 * of integers, bytes, structs and arrays, passed to functions and stored in a case class.
 * `Array.fill(n)` with a length known only at run time is a VLA, whose bound must be positive
 * even when `n` is 0.
 */
object EmptyArrays {

  case class P(x: Int, y: Int)

  case class Buffer(data: Array[Int], size: Int) {
    require(0 <= size && size <= data.length)
  }

  def len(a: Array[Int]): Int = a.length

  def count(a: Array[Int], x: Int): Int = {
    var c = 0
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i) == x) c += 1
      i += 1
    }).invariant(0 <= i && i <= a.length && 0 <= c && c <= i)
    c
  }

  def countOfFill(n: Int): Int = {
    require(0 <= n && n <= 100)
    count(Array.fill(n)(7), 7)
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    StdOut.println(len(Array[Int]()))           // 0
    val filled = Array.fill(0)(42)
    StdOut.println(count(filled, 42))           // 0
    val bytes = Array[Byte]()
    StdOut.println(bytes.length)                // 0
    val ps = Array[P]()
    StdOut.println(ps.length)                   // 0
    val b = Buffer(Array[Int](), 0)
    StdOut.println(b.data.length + b.size)      // 0
    val nested = Array[Array[Int]]()
    StdOut.println(nested.length)               // 0
    StdOut.println(countOfFill(0))              // 0
    StdOut.println(countOfFill(3))              // 3
  }
}
