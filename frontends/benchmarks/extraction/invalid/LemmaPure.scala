import stainless.annotation._

object LemmaPure {
  case class Box(@ghost var value: BigInt)

  // @lemma implies @pure
  @lemma def lem(b: Box): Unit = {
    b.value = 0
  }
}
