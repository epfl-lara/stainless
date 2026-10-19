import stainless.annotation._

object LemmaOpaque {
  // @lemma implies @opaque: the body of `id` is hidden from its callers
  @lemma def id(x: BigInt): BigInt = x

  @ghost def test(x: BigInt): Unit = assert(id(x) == x)
}
