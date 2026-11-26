import stainless.lang._

// `???` that is only a part of an executable body: a branch, a `val`, a match
// case and an argument.
object UnimplementedSubExpression {
  def branch(x: BigInt): BigInt = {
    if (x > 0) x else (??? : BigInt)
  }

  def binding(x: BigInt): BigInt = {
    val y = (??? : BigInt)
    x + y
  }

  def matching(o: Option[BigInt]): BigInt = o match {
    case Some(v) => v
    case None() => (??? : BigInt)
  }

  def id(x: BigInt): BigInt = x

  def argument: BigInt = id((??? : BigInt))

  def test: BigInt = {
    branch(0) + binding(1) + matching(None()) + argument
  }
}
