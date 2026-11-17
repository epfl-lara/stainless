import stainless.lang._
import stainless.collection._

object CakeSelfTypes {
  trait Exprs { self: Trees =>
    sealed abstract class Expr extends Tree
    case class IntLit(v: BigInt) extends Expr
    case class Plus(l: Expr, r: Expr) extends Expr

    final def lit(v: BigInt): Expr = IntLit(v)
    final def twice(e: Expr): BigInt = size(e) * 2
  }
  trait Trees extends Exprs { self =>
    abstract class Tree
    final def size(e: Expr): BigInt = {
      decreases(e)
      e match {
        case Plus(l, r) => size(l) + size(r) + 1
        case _ => BigInt(1)
      }
    }.ensuring(_ > 0)
  }
  case object trees extends Trees

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
  }

  def test: Unit = {
    assert(trees.twice(trees.Plus(trees.IntLit(1), trees.lit(2))) == 6)
  }
}
