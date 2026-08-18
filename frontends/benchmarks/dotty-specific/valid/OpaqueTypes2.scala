object OpaqueTypes2 {
  opaque type Positive <: BigInt = BigInt
  object Positive {
    def apply(b: BigInt): Positive = {
      require(b >= 0)
      b
    }
  }
}

// Unlike OpaqueTypes1, the opaque type is used outside its defining scope:
// `+` is available through the declared bound `<: BigInt`, but the receiver's
// type is the opaque alias, which extraction must resolve to dispatch the call.
object OpaqueTypes2Use {
  import OpaqueTypes2.*
  def test(p: Positive, q: Positive): BigInt = {
    p + q
  }

  def test2: BigInt = Positive(BigInt(1)) + Positive(BigInt(2))
}
