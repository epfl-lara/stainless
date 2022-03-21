import stainless.lang._
import stainless.collection._
import stainless.annotation._

object MutableKey4 {

  case class Box(var value: Int)

  def test(set: Bag[Box]): Unit = ()

}