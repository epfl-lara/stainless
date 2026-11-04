import stainless.lang._
object ReassignedInBothBranches {
  case class A(var x: Int)

  def test(cond: Boolean): Unit = {
    var x = A(1)
    val b = x
    if (cond) {
      x = A(2)
    } else {
      x = A(3)
    }
    
    x.x = 3
    assert(b.x == 1)
  }
}
