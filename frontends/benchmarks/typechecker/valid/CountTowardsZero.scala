import stainless.lang._

object Test {
  def f(x: BigInt): BigInt = {
    decreases(if (x < 0) -x else x)
    if (x == 0) {
      BigInt(0)
    } else if (x > 0) {
      f(x-1)+2
    } else if (x < 0) {
      f(x+1)-2
    } else {
      BigInt(33)
    }
  } ensuring (_ == x*2)
}
