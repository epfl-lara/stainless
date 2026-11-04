
object AntiAntiAliasing {
  case class Ref(var x: Int)
  case class RefRef(var lhs: Ref, var rhs: Ref)

  def replaceLhs(rr: RefRef, v: Int): Unit = {
    rr.lhs = Ref(v)
  }

  def t3(refref: RefRef): Unit = {
    val lhs = refref.lhs           // Point(p0)
    val oldLhs = lhs.x              // Point(p1)
    replaceLhs(refref, 123)           // Point(p2) [call: replaceLhs]
    assert(lhs.x == oldLhs)            // Point(p3)
    assert(refref.lhs.x == 123)         // Point(p4)
    refref.lhs.x = 456                   // Point(p5)
    assert(lhs.x == 456) // BUG: should be `oldLhs`, not 456   // Point(p6)
    assert(refref.lhs.x == 456)                                   // Point(p7)
  }
}
