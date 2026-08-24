package refinementMatch

type Pos = {i: Int with i > 0}

def checkNonNegative(b: Boolean): Boolean =
  val v = if b then 42 else 0
  v match
    case p : Pos => true
    case _ : {i: Int with i == 0} => true

case class Box(val value: Int)

def checkNonNegative2(b: Boolean): Boolean =
  val box = Box(if b then 42 else 0)
  box match
    case Box(p : Pos) => true
    case b @ Box(i: Int with i == 0) => true