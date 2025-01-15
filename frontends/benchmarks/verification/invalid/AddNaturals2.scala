import stainless.lang._
import stainless.annotation._
import stainless.collection._

object AddNaturals2 {
  def addNaturals(nats: List[Int]): Int = {
    require(nats.forall(((v: Int) => v >= 0 && v < 100000000))) // input list contains small nonnegative Ints
    nats.foldLeft(0)(_ + _)
  }.ensuring(_ >= 0) // function result is a nonnegative Int
}
