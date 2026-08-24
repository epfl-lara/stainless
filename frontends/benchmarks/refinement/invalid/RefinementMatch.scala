package refinementMatch

type Pos = {i: Int with i > 0}
case class Box(val value: Int)

def checkNonNegative2(b: Boolean): Boolean =
  val box = Box(if b then 42 else 0)
  box match
    case Box(p : Pos) => true