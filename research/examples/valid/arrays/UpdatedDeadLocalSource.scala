import stainless.lang._

object UpdatedDeadLocalSource {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Array(Box(1), Box(2))
    val b = a.updated(0, Box(0))

    b(1).value = 3

    assert(b(1).value == 3)
  }
}
