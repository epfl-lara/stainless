import stainless.lang._
import stainless.collection._

// Refinement types as type arguments, over classes of open hierarchies
object RefinedTypeArguments {
  abstract class Tree
  sealed abstract class Expr extends Tree
  case class Lit(v: BigInt) extends Expr

  def ok(e: Expr, b: BigInt): Boolean = e.isInstanceOf[Lit] && b > 0

  // Subtyping between refinements of different base types
  def lits(b: BigInt, n: BigInt): List[{ e: Expr with ok(e, b) }] = {
    require(b > 0 && n >= 0)
    decreases(n)
    if (n == 0) Nil() else Cons(Lit(n), lits(b, n - 1))
  }

  // The type of a method that is overridden depends on its parameters
  trait Source {
    def lits(b: BigInt): List[{ e: Expr with ok(e, b) }] = Nil()
  }

  abstract class Value
  case class Num(n: BigInt) extends Value

  // Pattern matching and measures on lists of refined values
  def count(b: BigInt, vs: List[{ v: Value with b > 0 }]): BigInt = {
    decreases(vs)
    vs match {
      case Cons(v, rest) => 1 + count(b, rest)
      case _ => BigInt(0)
    }
  }.ensuring(_ >= 0)
}
