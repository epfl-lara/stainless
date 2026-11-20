import stainless._
import stainless.lang._
import stainless.annotation._

object i1256 {

  case class Box(var value: Int)

  def test: Unit = {
    // Rejected due to binding a mutable type (an array) to a var.
    var arr = Array(Box(1))
    val arr2 = arr
    // After this assignment, arr and arr2 will become unrelated
    arr = Array(Box(42))
    arr2(0).value = 2
    assert(arr2(0).value == 2)
    assert(arr(0).value == 42)
  }

}
