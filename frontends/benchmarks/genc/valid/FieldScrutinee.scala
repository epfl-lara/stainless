import stainless.annotation.*
import stainless.io.*
import stainless.lang.*

/** Field selections (`r.dir`, `w.robot.dir`, `t._2`, ...) as match scrutinees.
 *  GenC binds the scrutinee to a temporary, so it is evaluated once: a case
 *  body that reassigns the field does not change what the pattern binders refer
 *  to. When the field has a mutable type, the temporary points to the field, so
 *  mutations through the binders reach the original object.
 */
object FieldScrutinee:

  sealed abstract class Direction
  case class North() extends Direction
  case class South() extends Direction

  sealed abstract class Command
  case class Move(steps: Int) extends Command
  case class Stop() extends Command

  case class Robot(var y: Int, var dir: Direction, var cmd: Command)

  case class World(robot: Robot, time: Int)

  case class Counter(var n: Int)

  case class Box(var counter: Counter, id: Int)

  sealed abstract class Shape
  case class Circle(var radius: Int) extends Shape
  case class Square(var side: Int) extends Shape

  case class Holder(var shape: Shape, id: Int)

  def dirCode(d: Direction): Int = d match
    case North() => 0
    case South() => 1

  def step(r: Robot, n: Int): Unit =
    require(0 <= n && n <= 1000)
    require(-1000 <= r.y && r.y <= 1000)
    r.dir match
      case North() => r.y += n
      case South() => r.y -= n

  def steps(r: Robot): Int = r.cmd match
    case Move(n) if n > 0 => n
    case Move(_) => 0
    case Stop() => -1

  /** The binder `d` is used after `r.dir` is reassigned and still refers to the
   *  old direction.
   */
  def flip(r: Robot): Int = {
    r.dir match
      case d @ North() =>
        r.dir = South()
        dirCode(d)
      case d @ South() =>
        r.dir = North()
        dirCode(d)
  }.ensuring(res => res == dirCode(old(r).dir) && dirCode(r.dir) == 1 - res)

  def bump(b: Box): Unit = {
    require(b.counter.n < 100)
    b.counter match
      case c @ Counter(_) => c.n += 1
  }.ensuring(_ => b.counter.n == old(b).counter.n + 1)

  def grow(h: Holder): Unit =
    require(h.shape match
      case Circle(radius) => radius < 100
      case Square(side) => side < 100
    )
    h.shape match
      case c @ Circle(_) => c.radius += 1
      case s @ Square(_) => s.side += 2

  def size(h: Holder): Int = h.shape match
    case Circle(radius) => radius
    case Square(side) => side

  def worldDir(w: World): Int = w.robot.dir match
    case North() => 10
    case South() => 20

  def makeRobot(): Robot = Robot(0, South(), Stop())

  def madeDir(): Int = makeRobot().dir match
    case North() => 100
    case South() => 200

  def tupleDir(t: (Int, Direction)): Int =
    require(0 <= t._1 && t._1 <= 1000)
    t._2 match
      case North() => t._1
      case South() => 1000 + t._1

  def elementDir(rs: Array[Robot], i: Int): Int =
    require(0 <= i && i < rs.length)
    rs(i).dir match
      case North() => 7
      case South() => 8

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState

    val r: Robot = Robot(0, North(), Move(5))
    step(r, 3)
    StdOut.println(r.y) // 3
    StdOut.println(steps(r)) // 5
    r.cmd = Move(0)
    StdOut.println(steps(r)) // 0
    r.cmd = Stop()
    StdOut.println(steps(r)) // -1
    StdOut.println(flip(r)) // 0
    StdOut.println(dirCode(r.dir)) // 1
    step(r, 1)
    StdOut.println(r.y) // 2
    StdOut.println(flip(r)) // 1
    StdOut.println(dirCode(r.dir)) // 0

    val b: Box = Box(Counter(41), 0)
    bump(b)
    StdOut.println(b.counter.n) // 42

    val h: Holder = Holder(Circle(3), 0)
    grow(h)
    StdOut.println(size(h)) // 4
    h.shape = Square(5)
    grow(h)
    StdOut.println(size(h)) // 7

    StdOut.println(worldDir(World(Robot(0, South(), Stop()), 0))) // 20
    StdOut.println(madeDir()) // 200

    // GenC types a tuple literal by its elements, so `(9, South())` would become a
    // `Tuple_int32_South` struct, incompatible with `Tuple_int32_Direction`
    val d: Direction = South()
    val t: (Int, Direction) = (9, d)
    StdOut.println(tupleDir(t)) // 1009

    val rs: Array[Robot] = Array(Robot(0, North(), Stop()), Robot(0, South(), Stop()))
    StdOut.println(elementDir(rs, 1)) // 8
