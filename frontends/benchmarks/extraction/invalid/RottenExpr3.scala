object RottenExpr3 {
  case class C1(var c2: C2)
  case class C2(var c3: C3)
  case class C3(var bi: BigInt)

  sealed trait Fish
  case class Trout(c11: C1, c12: C1) extends Fish
  case class Cod(c1: C1, c2: C2) extends Fish
  case class Salmon(c1: C1, c3: C3) extends Fish

  def test(c11: C1, x: BigInt): Fish = {
    require(x >= 0)
    val c12 = C1(C2(C3(x)))
    // This is not a fresh fish, therefore `test` cannot be recursive
    val f: Fish = Trout(c11, c12)
    if (x == 0) f
    else test(c11, x - 1)
  }
}