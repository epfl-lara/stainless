import stainless.lang._

class IllegalArgumentException(msg: String) extends Exception

object Throw {
  def f_throw_unreachable(x: BigInt): BigInt = {
    require(x >= 0)
    if (x < 0) then
      throw new IllegalArgumentException("x should not be negative")

    x + 1
  } ensuring(res => res >= 1)

  def g_throw_unreachable_in_while(x: BigInt): BigInt = {
    var i: BigInt = 0
    var acc: BigInt = 0
    (while( x * x + i < Int.MaxValue) do
      decreases(Int.MaxValue - x * x - i)
      val y = x * x + i
      acc = acc + y
      i = i + 1

      if (i < 0 || acc < 0) then
        throw new IllegalArgumentException("i and acc should not be negative")

    ) invariant(i >= 0 && acc >= 0)

    acc

  } ensuring(res => res >= 0)

}
