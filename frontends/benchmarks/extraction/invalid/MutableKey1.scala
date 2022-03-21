import stainless.lang._
import stainless.collection._
import stainless.annotation._

object MutableKey1 {

  case class Box(var value: Int)

  def test(map: Map[Box, BigInt]): Unit = ()

}