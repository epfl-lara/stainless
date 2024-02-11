import stainless.annotation._

object Purity5 {
  trait SomeTrait {
    def sum(b1: Box, b2: Box): BigInt
  }
  case class Box(var value: BigInt)

  def test(st: SomeTrait, b1: Box, @pure b2: Box): BigInt = st.sum(b1, b2)
}
