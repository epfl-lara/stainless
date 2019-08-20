import stainless.annotation._

object NonGhostUpdate {
  case class C(
    @ghost a: BigInt,
    b: BigInt,
    @ghost c: BigInt,
    d: BigInt,
    @ghost e: BigInt
  )

  def nonGhostUpdate(c: C): C = {
    c.copy(d = 0)
  }
}
