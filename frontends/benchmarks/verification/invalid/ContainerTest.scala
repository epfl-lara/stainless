import stainless.annotation._

object ContainerTest {
  case class Box(var value: BigInt)
  case class Container[T](t: T)

  @extern
  def f2(b: Container[Box]): Unit = ???

  def g2(b: Container[Box]) = {
    val b0 = b
    f2(b)
    assert(b == b0) // fails because `Container` is mutable
  }
}
