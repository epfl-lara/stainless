import stainless.annotation._

object Purity4 {

  case class Box(var value: BigInt)

  def test(b1: Box, @pure b2: Box): Unit = {
    externFn(b1, b2)
  }

  @extern
  def externFn(b1: Box, b2: Box): Unit = {
    ???
  }

}
