import stainless.annotation._
import stainless.collection._

object PreInPre {

  @induct
  def f(t: List[BigInt], st: BigInt): Unit = {
    require(t.head == st)
    ()
  }

}
