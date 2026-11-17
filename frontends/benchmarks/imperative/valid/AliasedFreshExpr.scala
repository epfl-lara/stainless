object AliasedFreshExpr {
  case class C1(var c2: C2)
  case class C2(var c3: C3)
  case class C3(var bi: BigInt)

  sealed trait Fish
  case class Trout(c11: C1, c12: C1) extends Fish
  case class Cod(c1: C1, c2: C2) extends Fish
  case class Salmon(c1: C1, c3: C3) extends Fish

  def test1(x: BigInt): Fish = {
    val c1 = C1(C2(C3(x)))
    // This expression is fresh, but is not alias-free
    Trout(c1, c1)
  }
}