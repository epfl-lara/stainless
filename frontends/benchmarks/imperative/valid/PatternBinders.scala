import stainless.lang._

object PatternBinders {
  case class Box(var value: BigInt)
  case class Holder(b: Box)
  case class Pair(left: Box, right: Holder)

  def f: Unit = {
    val a = Box(1)
    val b = Box(2)
    val p = Pair(a, Holder(b))
    val q = p match {
      case Pair(l, Holder(inner)) if l.value > 0 => inner
      case _ => a
    }
    val t = (a, b)
    val r = t match {
      case (_, w) => w
    }

    assert(q.value == 2)
    assert(r.value == 2)
  }
}
