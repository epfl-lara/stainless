import stainless.annotation._
import stainless.lang._
import stainless.io._

/**
 * End-to-end test of classic in-place array algorithms in GenC:
 *  - arrays passed to functions and mutated in place (insertion sort, reverse);
 *  - nested while loops with short-circuit conditions guarding array accesses;
 *  - a read-only binary search and a reduction (sum);
 *  - printing an array element by element.
 */
object ArrayAlgorithms {

  def insertionSort(a: Array[Int]): Unit = {
    val n = a.length
    var i = 0
    (while (i < n) {
      decreases(n - i)
      val key = a(i)
      val i0 = i // the inner loop leaves `i` unchanged, but its invariant has to say so
      var j = i - 1
      (while (j >= 0 && a(j) > key) {
        decreases(j + 1)
        a(j + 1) = a(j)
        j -= 1
      }).invariant(i == i0 && -1 <= j && j < i && i < n && a.length == n)
      a(j + 1) = key
      i += 1
    }).invariant(0 <= i && i <= n && a.length == n)
  }

  def reverse(a: Array[Int]): Unit = {
    var i = 0
    var j = a.length - 1
    (while (i < j) {
      decreases(j - i)
      val tmp = a(i)
      a(i) = a(j)
      a(j) = tmp
      i += 1
      j -= 1
    }).invariant(0 <= i && j < a.length && i + j == a.length - 1)
  }

  // Lower-bound binary search: index of `key` in the sorted array `a`, or -1.
  def binarySearch(a: Array[Int], key: Int): Int = {
    var lo = 0
    var hi = a.length
    (while (lo < hi) {
      decreases(hi - lo)
      val mid = lo + (hi - lo) / 2
      if (a(mid) < key) lo = mid + 1
      else hi = mid
    }).invariant(0 <= lo && lo <= hi && hi <= a.length)
    if (lo < a.length && a(lo) == key) lo else -1
  }

  def sum(a: Array[Int]): Int = {
    var s = 0
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      s += a(i)
      i += 1
    }).invariant(0 <= i && i <= a.length)
    s
  }

  def printArray(a: Array[Int])(implicit @ghost state: State): Unit = {
    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      if (i > 0) StdOut.print(' ')
      StdOut.print(a(i))
      i += 1
    }).invariant(0 <= i && i <= a.length)
    StdOut.println()
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState

    val a = Array(42, -7, 19, 0, 3, 19, -100, 8)
    printArray(a)                           // 42 -7 19 0 3 19 -100 8
    insertionSort(a)
    printArray(a)                           // -100 -7 0 3 8 19 19 42
    StdOut.println(binarySearch(a, 19))     // 5
    StdOut.println(binarySearch(a, 5))      // -1
    StdOut.println(binarySearch(a, -100))   // 0
    StdOut.println(binarySearch(a, 42))     // 7
    StdOut.println(sum(a))                  // -16
    reverse(a)
    printArray(a)                           // 42 19 19 8 3 0 -7 -100
  }
}
