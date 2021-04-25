import stainless.annotation._

object ContainerTest {
  case class Box(var value: BigInt)
  case class Container[@mutable T](t: T)

  @extern
  def f2(b: Container[Box]): Unit = ???

  def g2(b: Container[Box]) = {
    val v = b.t.value
    f2(b)
    assert(b.t.value == v)
  }
}
