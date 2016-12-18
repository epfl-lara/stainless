import stainless.lang._

object ArrayParamMutation6 {

  def multipleEffects(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0)
    a1(0) = 11
    a2(0) = 12
  } ensuring(_ => a1(0) != a2(0))

  def f(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0)
    multipleEffects(a1, a2)
  } ensuring(_ => a1(0) == 11 && a2(0) == 12)

}
