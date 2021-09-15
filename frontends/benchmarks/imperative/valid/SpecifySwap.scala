import stainless.lang._
import stainless.annotation._
import scala.Predef.{ genericArrayOps => _, genericWrapArray => _, copyArrayToImmutableIndexedSeq => _, _ }

object SpecifySwap {

  @extern @pure
  def property[T](a: Array[T]): Boolean = {
    (??? : Boolean)
  }

  @extern @pure
  def propertyAfterSwap[T](a: Array[T], i: Int, j: Int): Unit = {
    require(
      0 <= i && i < a.length &&
      0 <= j && j < a.length
    )

  }.ensuring(_ =>
    property(a.updated(i, a(j)).updated(j, a(i)))
  )

  def checkSwap[T](a: Array[T], i: Int, j: Int): Unit = {
    require(
      0 <= i && i < a.length &&
      0 <= j && j < a.length
    )

    propertyAfterSwap(a, i, j)

    swap(a, i, a, j)

    assert(property(a))
  }
}
