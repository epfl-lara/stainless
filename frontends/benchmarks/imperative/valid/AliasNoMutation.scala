import stainless.lang._

object AliasNoMutation {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Box(4)
    var b = a

    assert(b.value == 4)
  }
}
