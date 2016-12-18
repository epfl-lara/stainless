import stainless.lang._

object ArrayParamMutation2 {

  def rec(a: Array[BigInt]): BigInt = {
    require(a.length > 1 && a(0) >= 0)
    if(a(0) == 0) 
      a(1)
    else {
      a(0) = a(0) - 1
      a(1) = a(1) + a(0)
      rec(a)
    }
  } ensuring(res => a(0) == 0)

}
