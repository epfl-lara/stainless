object i1099cValid {
  case class A(var x: Int)
  case class C(a: A)

  sealed trait Scrut
  case class Case1(x: BigInt) extends Scrut
  case class Case2(x: BigInt, y: BigInt) extends Scrut
  case class Case3(abc: BigInt) extends Scrut

  def f(a0: A, a1: A, a2: A, scrut: Scrut) = {
    require(a0.x == 0 && a1.x == 1 && a2.x == 2)
    val a3 = scrut match {
      case Case1(x) => a0
      case Case2(x, y) if x + y == 42 => a1
      case _ => a2
    }
    val c = C(a3)
    c.a.x += 1
    scrut match {
      case Case1(x) => assert(a0.x == 1 && a1.x == 1 && a2.x == 2)
      case Case2(x, y) if x + y == 42 => assert(a0.x == 0 && a1.x == 2 && a2.x == 2)
      case _ => assert(a0.x == 0 && a1.x == 1 && a2.x == 3)
    }
  }
}
