
object MutableListFill {
  sealed abstract class MutableList
  case class MutableCons(var head: Int, tail: MutableList) extends MutableList
  case class MutableNil() extends MutableList

  // This function is recursive but returns fresh results, so it is valid
  def fill(size: Int, value: Int): MutableList =
    if (size <= 0) MutableNil()
    else MutableCons(value, fill(size - 1, value))
}
