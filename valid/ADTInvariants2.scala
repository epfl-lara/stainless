import leon.lang._

object ADTInvariants2 {
  case class Pos(i: BigInt) {
    require(i > 0)
  }

  def test(p: Pos): Boolean = {
    Pos(p.i + 1).i > 0
  }.holds

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  case class C(l: Cons)

  def test3(c: C): Boolean = {
    c.l.isInstanceOf[Cons]
  }.holds
}
