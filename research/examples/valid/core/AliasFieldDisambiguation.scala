import stainless.lang._

object AliasFieldDisambiguation {
  case class Box(var value: BigInt)
  case class Pair(left: Box, var right: Box)

  def f: Unit = {
    val a = Box(1)
    val p = Pair(a, Box(0))

    p.right = Box(99)

    assert(p.left.value == 1)
    assert(p.right.value == 99)

    a.value = 5

    assert(a.value == 5)
    assert(p.left.value == 5)
    assert(p.right.value == 99)
  }
}
