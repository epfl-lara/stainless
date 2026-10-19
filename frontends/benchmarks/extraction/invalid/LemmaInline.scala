import stainless.annotation._

object LemmaInline {
  // @lemma implies @inlineOnce, which conflicts with @inline
  @lemma @inline
  def lem(x: BigInt): Unit = ()
}
