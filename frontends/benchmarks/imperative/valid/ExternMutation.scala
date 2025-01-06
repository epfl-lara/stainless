import stainless.annotation._

object ExternMutation {
  case class Box(var value: BigInt)
  case class Container[@mutable T](t: T)

  @extern
  def f2(b: Container[Box]): Unit = ???

  def g2(b: Container[Box]) = {
    val b0 = b
    f2(b)
    assert(b == b0) // Ok, even though `b` is assumed to be modified because `b0` is an alias of `b`
  }
}
