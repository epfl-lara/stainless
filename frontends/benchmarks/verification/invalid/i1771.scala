import stainless.lang.*

object i1771:

  def f(b: BigInt): Any =
    require(b >= 0)
    b

  def g: Any =
    f(BigInt(-1))

  def h(b: BigInt): Any = {
    b
  }.ensuring(res => res > b)
