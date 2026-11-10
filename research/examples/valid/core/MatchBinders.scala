import stainless.lang._

object MatchBinders {
  case class Box(var value: BigInt)
  case class Holder(b: Box)

  def f: Unit = {
    var s = Holder(Box(1))
    s match {
      case Holder(y) =>
        y.value = 2
        assert(s.b.value == 2)
    }
  }

  def g: Unit = {
    var s = Holder(Box(1))
    s match {
      case Holder(y) =>
        s.b.value = 3
        assert(y.value == 3)
    }
  }

  def h: Unit = {
    var s = Holder(Box(1))
    s match {
      case t @ Holder(_) =>
        t.b.value = 4
        assert(s.b.value == 4)
    }
  }

  def k: Unit = {
    val a = Box(1)
    val t = (a, Box(2))
    t match {
      case (u, _) =>
        u.value = 5
        assert(a.value == 5)
    }
  }
}
