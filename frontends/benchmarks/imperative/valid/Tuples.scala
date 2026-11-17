import stainless.lang._

object Tuples {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Box(1)
    val t = (a, Box(2))
    val b = t._1
    val c = t._2

    b.value = 3

    assert(a.value == 3)
    assert(c.value == 2)
  }

  def g(t: (Box, Box)): BigInt = {
    val u = t._2
    u.value
  }
}
