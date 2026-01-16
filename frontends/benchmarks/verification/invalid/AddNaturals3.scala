import stainless.lang._
import stainless.annotation._
import stainless.collection._

object AddNaturals3 {
  def addTwoNaturals(x: Int, y: Int): Int = {
    require(x >= 0 && y >= 0)
    x + y
  }.ensuring(_ >= 0)
}
