import stainless.lang._

object AliasInLocalFunction {
  case class Box(var value: BigInt)

  def f: Unit = {
    def mutate: Unit = {
      var a = Box(4)
      var b = a

      a.value = 5

      assert(b.value == 5)
    }

    mutate
  }
}
