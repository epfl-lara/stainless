import stainless.lang._
import stainless.collection._
import stainless.annotation._

object MutableKey2 {

  case class Box(var value: Int)

  def test(map: MutableMap[Box, BigInt]): Unit = ()

}