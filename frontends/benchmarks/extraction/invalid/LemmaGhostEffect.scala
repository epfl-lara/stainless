import stainless.annotation._

object LemmaGhostEffect {
  case class Box(var value: BigInt)

  // @lemma implies @ghost
  @lemma def lem(b: Box): Unit = {
    b.value = 0
  }
}
