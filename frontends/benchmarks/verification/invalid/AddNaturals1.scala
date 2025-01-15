import stainless.lang._
import stainless.annotation._
import stainless.collection._

object AddNaturals1 {
  def addNaturals(nats: List[Int]): Int = {
    require(nats.forall(_ >= 0)) // input list contains nonnegative Ints
    nats.foldLeft(0)(_ + _)
  }.ensuring(_ >= 0) // function result is a nonnegative Int
}
