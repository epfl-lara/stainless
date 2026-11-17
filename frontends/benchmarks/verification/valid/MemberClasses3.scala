import stainless.lang._
import stainless.collection._

// Path-dependent types in type arguments, in methods of the cake and outside of it
object MemberClasses3 {
  trait Exprs {
    abstract class Expr
    case class Lit(v: BigInt) extends Expr
    case class Neg(e: Expr) extends Expr

    final def lits(n: BigInt): List[Expr] = {
      require(n >= 0)
      decreases(n)
      if (n == 0) Nil() else Cons(Lit(n), lits(n - 1))
    }.ensuring(_.size == n)

    final def negs(es: List[Expr]): List[Expr] = {
      decreases(es)
      es match {
        case Cons(e, rest) => Cons(Neg(e), negs(rest))
        case _ => Nil()
      }
    }.ensuring(_.size == es.size)
  }

  case object exprs extends Exprs

  def negLits(x: Exprs, n: BigInt): List[x.Expr] = {
    require(n >= 0)
    x.negs(x.lits(n))
  }.ensuring(_.size == n)

  def first(x: Exprs)(es: List[x.Expr]): x.Expr = {
    require(es.nonEmpty)
    es.head
  }

  def test: exprs.Expr = first(exprs)(negLits(exprs, 2))
}
