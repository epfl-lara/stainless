import stainless.lang._

// `???` inside first-class functions must be unreachable wherever the function
// value flows.
object UnimplementedLambda {
  def twice(f: BigInt => BigInt, x: BigInt): BigInt = f(f(x))

  def pick(b: Boolean): BigInt => BigInt = {
    if (b) (x: BigInt) => x + 1
    else (x: BigInt) => (??? : BigInt)
  }

  def test: BigInt = {
    twice(pick(false), 1)
  }
}
