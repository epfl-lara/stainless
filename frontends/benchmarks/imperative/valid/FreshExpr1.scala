import stainless.lang._

object FreshExpr1 {
  case class C1(var c2: C2)
  case class C2(var c3: C3)
  case class C3(var bi: BigInt)

  // This builds a fresh C2 because we build a fresh C3
  def buildCopyFromC2(c2: C2): C2 = C2(buildCopyFromC3(c2.c3))

  def buildCopyFromC3(c3: C3): C3 = C3(c3.bi)

  def test1(x: BigInt): Unit = {
    val c1 = C1(C2(C3(x)))
    // This is a fresh expression, so we can refer to
    // `c1` and `c2Cpy` freely in the remaining body
    val c2Cpy = buildCopyFromC2(c1.c2)
    c1.c2.c3.bi = 3
    assert(c1.c2.c3.bi == 3)
    assert(c2Cpy.c3.bi == x)
  }

  sealed trait Fish
  case class Trout(c11: C1, c12: C1) extends Fish
  case class Cod(c1: C1, c2: C2) extends Fish
  case class Salmon(c1: C1, c3: C3) extends Fish

  def swapped(c1: C1): C1 = C1(C2(C3(-c1.c2.c3.bi)))

  def pickC2(c1: C1): C2 = c1.c2

  def test2(x: BigInt): Fish = {
    require(x >= 0)
    decreases(x)
    val c11 = C1(C2(C3(x)))
    val c12 = swapped(c11)
    // `test2` returns a fresh fish therefore, it is allowed to be recursive.
    // However, note that we are not allowed to refer to `c11` or `c12`
    // in the remaining of the function, because val-binding require the value
    // to be bound *fresh w.r.t. an empty context* (i.e. `c11` and `c12` are
    // considered abstract because we "forget" their values).
    val f: Fish = Trout(c11, c12)
    val c2 = f match {
      case Trout(c11, _) => pickC2(c11)
    }
    c2.c3.bi = 3
    assert(f match {
      case Trout(c11, _) => c11.c2.c3.bi == 3
    })
    if (x == 0) f
    else test2(x - 1)
  }

  // Similar to `test2` but tests pattern matching freshness propagation
  def test3(x: BigInt): C1 = {
    require(x >= 0)
    decreases(x)
    val c11 = C1(C2(C3(x)))
    val c12 = swapped(c11)
    val f: Fish = Trout(c11, c12)
    val c2 = f match {
      case Trout(c11, _) => pickC2(c11)
    }
    c2.c3.bi = 3
    assert(f match {
      case Trout(c11, _) => c11.c2.c3.bi == 3
    })
    if (x == 0) f match {
      case Trout(c11, _) => c11
    }
    else test3(x - 1)
  }
}