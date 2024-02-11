import stainless.lang._
import stainless.annotation._

object TargetMutation6 {
  case class Ref(var x: Int)
  case class RefRef(var lhs: Ref, var rhs: Ref)

  def replaceLhs(rr: RefRef, v: Int): Unit = {
    rr.lhs = Ref(v)
  }

  def t1(arr1: Array[Ref], arr2: Array[Ref], i: Int, j: Int, k: Int, cond: Boolean, gra: Ref): Unit = {
    require(arr1.length >= 10)
    require(arr2.length >= arr1.length)
    require(0 <= i && i < arr1.length)
    require(0 <= j && j < arr1.length)
    require(0 <= k && k < arr1.length)

    val someElem = arr1(0)
    val oldSomeElem = someElem.x
    swap(arr1, 0, arr2, 1)
    assert(someElem.x == oldSomeElem)
  }

  def t2(refref: RefRef): Unit = {
    val lhs = refref.lhs
    val oldLhs = lhs.x
    refref.lhs = Ref(123)
    assert(lhs.x == oldLhs)
  }

  def t3(refref: RefRef): Unit = {
    val lhs = refref.lhs
    val oldLhs = lhs.x
    replaceLhs(refref, 123)
    assert(lhs.x == oldLhs)
  }
}
