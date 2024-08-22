import stainless._
import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._

object i1271g {

  @pure
  def upd(arr: Array[BigInt], i: Int): (Array[BigInt], Int) = {
    require(0 <= i && i < arr.length - 10)
    (freshCopy(arr).updated(i, 1234), 1234)
  }

  @opaque
  @inlineOnce
  def looping_app(arr: Array[BigInt], i: Int): Int = {
    decreases(i)
    require(0 <= i && i < arr.length - 10)
    val (arr2, x) = upd(arr, i)

    {
      if (i == 0) i
      else {
        val (arr3, xyz) = upd(arr2, i)
        looping_app(arr3, looping_app(arr3, 1 + i - 1))
      }
   }.ensuring { r => 0 <= r && r < arr.length - 10 }
  }
}
