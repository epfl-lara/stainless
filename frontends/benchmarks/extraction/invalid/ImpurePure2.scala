import stainless.annotation.pure

object ImpurePure2 {
  case class Box(var value: Int)

  @pure
  def outer(b: Box): Unit = { // A lying "pure" function!
    def inner: Unit = {
      b.value = 1234
    }
  }
}