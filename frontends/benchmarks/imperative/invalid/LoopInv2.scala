import stainless.lang._
import stainless.annotation._
import stainless.collection._

object LoopInv2 {

  sealed abstract class Input
  case object Plus extends Input
  case object Minus extends Input

  val empty = Nil[Input]()

  val S  = Set(0, 1, 2, 3, 4, 5, 6)
  val G1 = Set(0, 1, 2, 4, 5, 6)
  val G2 = Set(4, 5, 6)
  val G3 = Set(0, 2, 4, 6)

  def check(inputs: List[Input]) = {
    var remains = inputs
    var left    = true
    var state   = 0

    (while (left) {
      remains match {
        case Nil() =>
          left = false

        case Cons(input, _) =>
          input match {
            case Plus  if state <= 4 => state += 2
            case Minus if state >= 2 => state -= 2
            case _                   => ()
          }

          remains = remains.tail
      }
    }) invariant (G2.contains(state)) // INVALID
  }

}


