import stainless._
import stainless.lang._
import stainless.annotation._

object i1333 {

  @pure
  def upd(arr: Array[BigInt], i: Int): (Array[BigInt], Int) = {
    require(0 <= i && i < arr.length - 10)
    (freshCopy(arr).updated(i, 1234), 1234)
  }

  def app(arr: Array[BigInt], i: Int): Unit = {
    decreases(i)
    require(0 <= i && i < arr.length - 10)
    val (arr2, x) = upd(arr, i)

    {
      if (i == 0) ()
      else {
        val (arr3, xyz) = upd(arr2, i)
        app(arr3, i - 1)
      }
   }.ensuring { _ => i < arr.length }
  }
}
