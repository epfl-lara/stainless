import stainless.lang._
import stainless.annotation._

object ChooseByExtern {

  @extern
  def universalEquality(a: BigInt): BigInt = {
    ??? : BigInt // Replaced by a choose over the postcondition
  }.ensuring(r => r == 42 && r == 24)

  def theorem(): Unit = {
    val x = universalEquality(0)
    assert(x == 42 && x == 24)
    assert(false)
    ()
  }
}
