import stainless.lang._
import stainless.collection._
import stainless.annotation._

// Member classes: classes nested in classes and traits, referring to their enclosing instances
object MemberClasses2 {
  trait Base {
    abstract class Tree {
      def depth: BigInt
    }
    final def zero: BigInt = 0
  }

  trait Exprs extends Base {
    sealed abstract class Expr extends Tree
    case class Lit(v: BigInt) extends Expr {
      def depth: BigInt = Exprs.this.zero
    }
    case class Neg(e: Expr) extends Expr {
      def depth: BigInt = e.depth + 1
      def negLit: Expr = Neg(Lit(v = 0))
    }

    class Counter(val n: BigInt) {
      def next: Counter = new Counter(n + 1)
      class Step(val k: BigInt) {
        def total: BigInt = n + k + zero
      }
      def step: Step = new Step(1)
    }


    def isLit(e: Expr): Boolean = e match {
      case _: Lit => true
      case _ => false
    }
  }

  case object ex extends Exprs
  case object ey extends Exprs

  def depths(x: Exprs)(es: List[x.Expr]): List[BigInt] = es.map(_.depth)

  def test1: BigInt = {
    val c = new ex.Counter(41)
    val s = c.next.step
    assert(s.total == 43)
    s.total
  }

  def test2(e: ex.Expr): Boolean = {
    e.isInstanceOf[ex.Lit] == ex.isLit(e)
  }

  def test3: ex.Expr = ex.Neg(ex.Lit(1)).negLit

  def lits(x: Exprs, n: BigInt): List[x.Expr] = {
    require(n >= 0)
    decreases(n)
    if (n == 0) Nil() else Cons(x.Lit(n), lits(x, n - 1))
  }

  def test4: Unit = {
    val l = lits(ex, 3)
    assert(l.size == 3)
    assert(depths(ex)(l) == List[BigInt](0, 0, 0))
  }
}
