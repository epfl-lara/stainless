import stainless.lang._

object MultipleMutableRef {
  case class Box(var value: BigInt)
  case class Wrap[T](v: T)

  def f: Unit = {
    var x = Wrap(Box(4))
    var y = x

    assert(y.v.value == 4)
  }
}
