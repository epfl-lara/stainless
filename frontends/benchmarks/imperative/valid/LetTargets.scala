import stainless.lang._
import stainless.annotation._

object LetTargets {

  case class A(var x: Int)
  case class B(as: Array[A])
  case class C(bs: Array[B])
  case class D(val c: C)

  @cCode.`export`
  def reset(d: D): Unit = {
    require(d.c.bs.length > 0)
    require(d.c.bs(0).as.length > 0)

    {
      val b: B = d.c.bs(0)
      b
    }.as(0).x = 0
  }

  def test(d: D): Unit = {
    require(d.c.bs.length > 0)
    require(d.c.bs(0).as.length > 0)
    reset(d)
    assert(d.c.bs(0).as(0).x == 0)
  }
}
