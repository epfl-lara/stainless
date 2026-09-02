// Unsoundness due to an incorrect AntiAliasing transformation
// See https://github.com/epfl-lara/stainless/issues/1506
object i1506 {
  case class Ref(var x: Int)
  case class RefRef(var lhs: Ref, var rhs: Ref)

  def replaceLhs(rr: RefRef, v: Int): Unit = {
    rr.lhs = Ref(v)
  }

  def t3(refref: RefRef): Unit = {
    val lhs = refref.lhs
    val oldLhs = lhs.x
    replaceLhs(refref, 123)
    assert(lhs.x == oldLhs)
    assert(refref.lhs.x == 123)
    refref.lhs.x = 456
    assert(lhs.x == 456) // Incorrect because `lhs` and `refref.lhs` become unrelated after the call to `replaceLhs`
    assert(refref.lhs.x == 456)
  }
}
