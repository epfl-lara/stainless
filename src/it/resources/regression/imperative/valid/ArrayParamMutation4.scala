import stainless.lang._

object ArrayParamMutation4 {

  def multipleArgs(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0)
    if(a1(0) == 10)
      a2(0) = 13
    else
      a2(0) = a1(0) + 1
  }

  def transitiveEffects(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0)
    multipleArgs(a1, a2)
  } ensuring(_ => a2(0) >= a1(0))

  def transitiveReverseEffects(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0)
    multipleArgs(a2, a1)
  } ensuring(_ => a1(0) >= a2(0))

}
