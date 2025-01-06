object RottenExpr1 {
  case class C1(var c2: C2)
  case class C2(var c3: C3)
  case class C3(var bi: BigInt)

  // This creates a C2 by sharing c2.c3 (which is mutable),
  // therefore, this expression is not fresh
  def buildFromC2Rotten(c2: C2) = C2(c2.c3)

  def test(x: BigInt): Unit = {
    val c1 = C1(C2(C3(x)))
    // This is not a fresh expression: we are not allowed to
    // refer to `c1` in the body (illegal aliasing).
    val c2Cpy = buildFromC2Rotten(c1.c2)
    c1.c2.c3.bi = 3
  }
}