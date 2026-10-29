import stainless.annotation._
import stainless.lang._
import stainless.io._

/**
 * End-to-end test of polymorphism in GenC:
 *  - a generic case class instantiated at several (including nested) types,
 *    each of which must become a distinct C struct;
 *  - generic functions instantiated at several types, each of which must
 *    become a distinct, correctly named C function;
 *  - tuples returned from functions and destructured at the call site;
 *  - `Option` returned from a loop and consumed by pattern matching;
 *  - named functions passed as first-class values (function pointers);
 *  - structural equality on generic structs.
 */
object GenericPairs {

  case class Pair[A, B](first: A, second: B)

  def swap[A, B](p: Pair[A, B]): Pair[B, A] = Pair(p.second, p.first)

  def first[A, B](p: Pair[A, B]): A = p.first

  def toTuple[A, B](p: Pair[A, B]): (A, B) = (p.first, p.second)

  def divMod(a: Int, b: Int): (Int, Int) = {
    require(b != 0)
    (a / b, a % b)
  }

  def minMax(a: Array[Int]): (Int, Int) = {
    require(a.length > 0)
    var lo = a(0)
    var hi = a(0)
    var i = 1
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i) < lo) lo = a(i)
      if (a(i) > hi) hi = a(i)
      i += 1
    }).invariant(0 <= i && i <= a.length)
    (lo, hi)
  }

  def double(x: Int): Int = x * 2
  def inc(x: Int): Int = x + 1
  def isEven(x: Int): Boolean = x % 2 == 0
  def isNegative(x: Int): Boolean = x < 0

  def applyTwice(f: Int => Int, x: Int): Int = f(f(x))

  def findFirst(a: Array[Int], p: Int => Boolean): Option[Int] = {
    var i = 0
    var res: Option[Int] = None[Int]()
    (while (res.isEmpty && i < a.length) {
      decreases(a.length - i)
      if (p(a(i))) res = Some(i)
      i += 1
    }).invariant(0 <= i && i <= a.length)
    res
  }

  def optionToInt(o: Option[Int]): Int = o match {
    case Some(v) => v
    case None()  => -1
  }

  def boolToInt(b: Boolean): Int = if (b) 1 else 0

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState

    val p = Pair(7, true)
    val q = swap(p)                                   // Pair[Boolean, Int]
    StdOut.println(q.second)                          // 7
    StdOut.println(boolToInt(first(q)))               // 1
    StdOut.println(boolToInt(swap(q) == p))           // 1
    StdOut.println(boolToInt(q == Pair(false, 7)))    // 0

    val nested = Pair(Pair(3, 4L), 'x')               // Pair[Pair[Int, Long], Char]
    StdOut.println(nested.first.first + nested.first.second.toInt) // 7
    StdOut.println(nested.second)                     // x

    val (q1, r1) = divMod(17, 5)
    StdOut.println(q1)                                // 3
    StdOut.println(r1)                                // 2
    val (q2, r2) = divMod(-17, 5)
    val t = toTuple(Pair(q2, r2))
    StdOut.println(t._1 * 10 + t._2)                  // -32

    val a = Array(5, -3, 9, 0, 12, 7)
    val (lo, hi) = minMax(a)
    StdOut.println(lo)                                // -3
    StdOut.println(hi)                                // 12

    StdOut.println(applyTwice(double, 7))             // 28
    StdOut.println(applyTwice(inc, 7))                // 9
    StdOut.println(optionToInt(findFirst(a, isEven)))        // 3
    StdOut.println(optionToInt(findFirst(a, isNegative)))    // 1
    StdOut.println(optionToInt(findFirst(Array(1, 3, 5), isEven))) // -1
  }
}
