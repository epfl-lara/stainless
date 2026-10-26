import stainless.annotation._

object LemmaGhost {
  // @lemma implies @ghost
  @lemma def lem(x: BigInt): Unit = ()

  def f(x: BigInt): Unit = {
    lem(x) // should be rejected
    ()
  }
}
