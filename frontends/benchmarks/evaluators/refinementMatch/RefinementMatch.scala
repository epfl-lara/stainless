object RefinementMatch {
  type Pos = {i: Int with i > 0}
  case class Box(val value: Int)

  def checkNonNegative(b: Boolean): Boolean =
    val box = Box(if b then 42 else 0)
    box match
      case Box(p : Pos) => true
      case b @ Box(i: Int with i == 0) => false

  def eval1 = checkNonNegative(true)
  def eval2 = checkNonNegative(false)

  def expected1 = true
  def expected2 = false
}
