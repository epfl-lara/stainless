import stainless.lang._

object CopyDeadResultAlias {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Array(Box(1), Box(2))
    val b = a

    a = a.updated(0, Box(7))
    b(1).value = 5
  }
}
