import stainless.lang._
import stainless.annotation._

// A cake: expression trees defined in a trait, so that each instance of the trait has its own trees
object MemberClasses1 {
  trait Trees {
    sealed abstract class Expr
    case class IntLit(v: BigInt) extends Expr
    case class Plus(l: Expr, r: Expr) extends Expr

    final def size(e: Expr): BigInt = {
      decreases(e)
      e match {
        case Plus(l, r) => size(l) + size(r) + 1
        case IntLit(_) => BigInt(1)
      }
    }.ensuring(_ > 0)

    final def two: Expr = Plus(IntLit(1), IntLit(1))
  }

  case object trees extends Trees
  case object others extends Trees

  // Path-dependent types: `s.Expr` and `t.Expr` are trees of the instances `s` and `t`
  trait Transformer {
    val s: Trees
    val t: Trees

    final def transform(e: s.Expr): t.Expr = {
      decreases(e)
      e match {
        case s.IntLit(v) => t.IntLit(v)
        case s.Plus(l, r) => t.Plus(transform(l), transform(r))
      }
    }.ensuring(res => t.size(res) == s.size(e))

    // Transforming trees into the same instance is the identity
    @ghost
    final def isIdentity(e: s.Expr): Unit = {
      require(s == t)
      decreases(e)
      e match {
        case s.Plus(l, r) => isIdentity(l); isIdentity(r)
        case _ => ()
      }
    }.ensuring(_ => transform(e) == e)
  }

  case class Copy(s: Trees, t: Trees) extends Transformer

  def sizes(tr: Transformer)(e: tr.s.Expr): BigInt = {
    val transformed = tr.transform(e)
    assert(tr.t.size(transformed) == tr.s.size(e))
    tr.t.size(transformed)
  }

  def twos: BigInt = trees.size(trees.two) + others.size(others.two)
}
