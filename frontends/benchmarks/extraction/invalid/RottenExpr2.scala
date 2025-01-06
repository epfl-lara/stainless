object RottenExpr2 {
  case class C1(var c2: C2)
  case class C2(var c3: C3)
  case class C3(var bi: BigInt)

  sealed trait Fish
  case class Trout(c11: C1, c12: C1) extends Fish
  case class Cod(c1: C1, c2: C2) extends Fish
  case class Salmon(c1: C1, c3: C3) extends Fish

  def swapped(c1: C1): C1 = C1(C2(C3(-c1.c2.c3.bi)))

  def pickC2(c1: C1): C2 = c1.c2

  def test(x: BigInt): Fish = {
    val c11 = C1(C2(C3(x)))
    val c12 = swapped(c11)
    // `test` returns a fresh fish.
    // However, we are not allowed to refer to `c11` or `c12`
    // in the remaining of the function, because val-binding require the value
    // to be bound *fresh w.r.t. an empty context* -- which is note the case
    // (`c11` and `c12` are to be considered abstract as if we were to "forget" their values).
    val f: Fish = Trout(c11, c12)
    // "Illegal aliasing" triggered due to these lines
    val c11bis = c11
    val c12bis = c12
    f
  }
}