import stainless.lang._
import stainless.collection._
import stainless.annotation._

object ArraySlice {

  def slice[A](array: Array[A], start: Int, end: Int): List[A] = {
    require(start >= 0 && end >= 0 && end <= array.length && end >= start)
    decreases(end - start)
    if (end - start == 0) Nil()
    else Cons(array(start), slice(array, start + 1, end))
  }

  def arr = Array(1,2,3,4)

  def test1 = {
    slice(arr, 0, 4) == List(1,2,3,4)
  }.holds

  def test2 = {
    slice(arr, 1, 4) == List(2,3,4)
  }.holds

  def test3 = {
    slice(arr, 2, 4) == List(3,4)
  }.holds

  def test4 = {
    slice(arr, 3, 4) == List(4)
  }.holds

  def test5 = {
    slice(arr, 4, 4) == Nil[Int]()
  }.holds

}
