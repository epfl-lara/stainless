import stainless.lang._
object ReassignedThenCopied {
  case class A(var x: Int)

  def test(cond: Boolean): Unit = {
    var a = A(1)
    if (cond) {
      a = A(2)
    }
    val b = a
    a.x = 5
    assert(b.x == 5)
  }
}
