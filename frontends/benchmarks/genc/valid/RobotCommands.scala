import stainless.annotation._
import stainless.lang._
import stainless.io._

/**
 * End-to-end test of algebraic data types in GenC:
 *  - a hierarchy whose leaves are all field-less (`Direction`), which GenC maps
 *    to a C enum;
 *  - a hierarchy with payloads (`Command`), which GenC maps to a tagged union;
 *  - an array of tagged-union values, iterated over in a loop;
 *  - a mutable case class (`Robot`) updated through a function call, including
 *    a `var` field of enum type;
 *  - pattern matching on both hierarchies, nested matches, and structural
 *    equality (`==`) on ADT values.
 */
object RobotCommands {

  sealed abstract class Direction
  case class North() extends Direction
  case class East() extends Direction
  case class South() extends Direction
  case class West() extends Direction

  sealed abstract class Command
  case class Move(steps: Int) extends Command
  case class TurnLeft() extends Command
  case class TurnRight() extends Command
  case class Teleport(x: Int, y: Int) extends Command

  case class Robot(var x: Int, var y: Int, var dir: Direction, var moves: Int)

  def turnLeft(d: Direction): Direction = d match {
    case North() => West()
    case West()  => South()
    case South() => East()
    case East()  => North()
  }

  def turnRight(d: Direction): Direction = d match {
    case North() => East()
    case East()  => South()
    case South() => West()
    case West()  => North()
  }

  def dirCode(d: Direction): Int = d match {
    case North() => 0
    case East()  => 1
    case South() => 2
    case West()  => 3
  }

  def step(r: Robot, c: Command): Unit = c match {
    case Move(n) =>
      // Note: GenC does not accept a field selection (`r.dir`) as a match
      // scrutinee, so it is bound to a local first.
      val d = r.dir
      d match {
        case North() => r.y += n
        case South() => r.y -= n
        case East()  => r.x += n
        case West()  => r.x -= n
      }
      r.moves += 1
    case TurnLeft()  => r.dir = turnLeft(r.dir)
    case TurnRight() => r.dir = turnRight(r.dir)
    case Teleport(x, y) =>
      r.x = x
      r.y = y
  }

  def run(r: Robot, cmds: Array[Command]): Unit = {
    var i = 0
    (while (i < cmds.length) {
      decreases(cmds.length - i)
      step(r, cmds(i))
      i += 1
    }).invariant(0 <= i && i <= cmds.length)
  }

  def boolToInt(b: Boolean): Int = if (b) 1 else 0

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState

    val r = Robot(0, 0, North(), 0)
    val cmds = Array[Command](
      Move(3), TurnRight(), Move(2), TurnRight(), Move(1),
      Teleport(10, -5), TurnLeft(), Move(4)
    )
    run(r, cmds)

    StdOut.println(r.x)                                        // 14
    StdOut.println(r.y)                                        // -5
    StdOut.println(dirCode(r.dir))                             // 1 (East)
    StdOut.println(r.moves)                                    // 4
    StdOut.println(boolToInt(r.dir == East()))                 // 1
    StdOut.println(boolToInt(r.dir == North()))                // 0
    StdOut.println(boolToInt(turnLeft(turnRight(r.dir)) == r.dir)) // 1
    StdOut.println(boolToInt(cmds(0) == Move(3)))              // 1
    StdOut.println(boolToInt(cmds(0) == Move(4)))              // 0
    StdOut.println(boolToInt(cmds(1) == cmds(3)))              // 1
  }
}
