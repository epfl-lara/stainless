object Inconsistency {
  def looping(c: BigInt): Boolean = !decode(c)(c)
  def decode(c: BigInt): BigInt => Boolean = looping _
  def encode(f: BigInt => Boolean): BigInt = 0

  def theorem() = {
    looping(encode(looping _)) // reduces to !looping(encode(looping _)), etc.
    assert(false)
  }
}
