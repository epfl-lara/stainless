import stainless.annotation._

object ContainerTest {
  case class Container[@mutable T](t: T)

  @extern
  def f(b: Container[BigInt]): Unit = ???

  def g(b: Container[BigInt]) = {
    val b0 = b
    f(b)
    assert(b == b0) // succeeds because `Container[BigInt]` is immutable
  }
}
