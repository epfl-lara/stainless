import stainless.lang._

// The trees of distinct instances of a cake cannot be mixed
object MemberClassesMixing {
  trait Trees {
    sealed abstract class Expr
    case class IntLit(v: BigInt) extends Expr
    case class Neg(e: Expr) extends Expr
  }

  case object trees extends Trees
  case object others extends Trees

  def mixed: others.Expr = trees.IntLit(1).asInstanceOf[others.Expr]

  def neg(s: Trees, t: Trees)(e: s.Expr): t.Expr = t.Neg(e.asInstanceOf[t.Expr])

  def outer(s: Trees)(e: Trees#Expr): BigInt = e match {
    case s.IntLit(v) => v
    case _ => 0
  }

  def outerTest: Unit = {
    assert(outer(trees)(others.IntLit(1)) == 1)
  }
}
