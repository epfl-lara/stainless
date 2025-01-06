import stainless._
import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._

object i1271f {

  @pure
  def upd(arr: Array[BigInt], i: Int): (Array[BigInt], Int) = {
    require(0 <= i && i < arr.length - 10)
    (freshCopy(arr).updated(i, 1234), 1234)
  }

  @opaque
  @inlineOnce
  def looping_app(arr: Array[BigInt], i: Int): Unit = {
    decreases(i)
    require(0 <= i && i < arr.length - 10)
    val (arr2, x) = upd(arr, i)

    {
      if (i == 0) ()
      else {
        val (arr3, xyz) = upd(arr2, i)
        looping_app(arr3, 1 + i - 1)
      }
   }.ensuring { _ => i < arr.length }
  }
}
