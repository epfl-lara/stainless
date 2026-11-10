import stainless.annotation.*
import stainless.io.*

/** Type aliases, which GenC replaces with what they stand for. */
object TypeAliases:

  @cCode.`export`
  type Pixel = Int

  type Colour = Pixel

  type Pair[A] = (A, A)

  type Pixels = Array[Pixel]

  case class Point(x: Pixel, y: Colour)

  type P = Point

  sealed trait Shape

  case class Dot(p: Point) extends Shape

  case class Empty() extends Shape

  type S = Shape

  @cCode.`export`
  def samePixel(x: Pixel): Pixel =
    val y: Pixel = x
    y

  def getX(p: P): Pixel =
    p.x

  def swapped(a: Int, b: Int): Pair[Int] =
    (b, a)

  def first(ps: Pixels): Pixel =
    require(ps.length == 3)
    val x: Pixel = ps(0)
    x

  def xOrZero(s: S): Int =
    s match
      case Dot(p) => p.x
      case Empty() => 0

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    StdOut.println(samePixel(10)) // 10
    val p: P = Point(1, 2)
    StdOut.println(getX(p)) // 1
    val q: (Int, Int) = swapped(3, 4)
    StdOut.println(q._1) // 4
    val ps: Pixels = Array(5, 6, 7)
    StdOut.println(first(ps)) // 5
    val s: S = Dot(Point(8, 9))
    StdOut.println(xOrZero(s)) // 8
