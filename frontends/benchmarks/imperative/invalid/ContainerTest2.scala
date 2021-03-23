import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ContainerTest2 {
  case class Box(var value: BigInt)
  case class Container[@mutable T](t: T)

  @extern
  def f2(b: Container[Box]): Unit = ???

  def g2(b: Container[Box]) = {
    @ghost val b0 = snapshot(b)
    f2(b)
    assert(b == b0)
  }
}
