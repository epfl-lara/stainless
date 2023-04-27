import stainless.annotation._

object ContainerTest {
  case class Box(var value: BigInt)
  case class Container[T](t: T)

  // T must be annotated with @mutable
  def f2(b: Container[Box]): Unit = ()
}
