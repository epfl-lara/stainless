
object ErasedTerms3 {

  erased def F(x: BigInt, y: BigInt): BigInt = {
    y
  }

  def G(x: BigInt)(erased y: BigInt): BigInt = {
    y // error: cannot return a ghost from a non-ghost function
  }

  def N(x: BigInt)(erased y: BigInt): BigInt = {
    x
  }

  erased def P(x: BigInt, y: BigInt): BigInt = {
    erased val r: BigInt = 0
    erased val g: BigInt = 5
    erased val h = N(20)(20)
    h
  }
}
