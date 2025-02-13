import stainless.lang._
import stainless.lang._
import stainless.annotation._

object AddNaturals4 {
  def addTwoNaturals(x: Int, y: Int): Int = {
    require(x >= 0 && y >= 0)
    x + y
  }.ensuring(_ >= 0)

  def addTwoBigNaturals(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0 && y >= 0)
    x + y
  }.ensuring(_ >= 0)

  def addTwoSmallNaturals(x: Int, y: Int): Int = {
    require(x >= 0 && y >= 0 && x < 1000000 && y < 1000000)
    x + y
  }.ensuring(_ >= 0)
}
