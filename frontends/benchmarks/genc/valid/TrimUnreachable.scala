import stainless.annotation._
import stainless.collection._

/**
 * `List` (a recursive type, unsupported by GenC) is only mentioned by code that
 * exported functions do not reach, so GenC must not try to translate it.
 * Exported and global classes must still be emitted even if no exported function uses them.
 */
object TrimUnreachable {

  case class State(var n: Int, @ghost var history: List[Int])

  case class Unused(l: List[Int] = Nil())

  @ghost
  def size(l: List[Boolean]): BigInt = l.size

  def unused(l: List[Int]): BigInt = l.size

  @cCode.`export`
  case class Point(x: Int, y: Int)

  @cCode.global
  case class Counter(var count: Int = 0)

  def unusedRoots(p: Point)(using c: Counter): Int = p.x

  @cCode.`export`
  def get(s: State): Int = s.n

  @cCode.`export`
  def main(): Unit = ()
}
