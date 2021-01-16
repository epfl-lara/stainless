import stainless.lang._

object ArrayParamMutation3 {

  def odd(a: Array[BigInt]): Boolean = {
    require(a.length > 0 && a(0) >= 0)
    if(a(0) == 0) false
    else {
      a(0) = a(0) - 1
      even(a)
    }
  } ensuring(res => a.length > 0 && a(0) == 0)

  def even(a: Array[BigInt]): Boolean = {
    require(a.length > 0 && a(0) >= 0)
    if(a(0) == 0) true
    else {
      a(0) = a(0) - 1
      odd(a)
    }
  } ensuring(res => a.length > 0 && a(0) == 0)

}
