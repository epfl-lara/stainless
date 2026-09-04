object NonErasedUpdate {
  case class C(
    erased a: BigInt,
    b: BigInt,
    erased c: BigInt,
    d: BigInt,
    erased e: BigInt
  )

  def nonErasedUpdate(c: C): C = {
    c.copy(d = 0)
  }
}
