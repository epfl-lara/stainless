
import stainless.lang._
import stainless.annotation._

object ArrayParamMutation5 {

  @inlineOnce
  def mutuallyRec1(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a1(0) > 0 && a2.length > 0)
    if(a1(0) == 10) {
      ()
    } else {
      mutuallyRec2(a1, a2)
    }
 }.ensuring(res => a1(0) == 10)

  def mutuallyRec2(a1: Array[BigInt], a2: Array[BigInt]): Unit = {
    require(a1.length > 0 && a2.length > 0 && a1(0) > 0)
    decreases(if (a1(0) == 10) 1 else 0)
    a1(0) = 10
    mutuallyRec1(a1, a2)
  }

}
