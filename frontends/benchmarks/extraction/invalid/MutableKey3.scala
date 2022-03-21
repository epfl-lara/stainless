import stainless.lang._
import stainless.collection._
import stainless.annotation._

object MutableKey3 {

  case class Box(var value: Int)

  def test(set: Set[Box]): Unit = ()

}