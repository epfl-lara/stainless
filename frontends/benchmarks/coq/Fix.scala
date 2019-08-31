import stainless.lang._

object Fix {
  def myfix(i: BigInt, j: BigInt):BigInt = {
    require(i > 0)
    myfix(i+1, j+1)
  } ensuring(res => (res > 0))
}
