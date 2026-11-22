import stainless.lang._
import stainless.annotation._
import stainless.collection._

sealed abstract class EvalError extends Exception
case class TypeError(msg: String) extends EvalError
case class DivByZero() extends EvalError
case class Other(code: BigInt) extends Exception

sealed abstract class Expr
case class Lit(v: BigInt) extends Expr
case class Div(l: Expr, r: Expr) extends Expr
case class Neg(e: Expr) extends Expr

object Exceptions2 {
  // Recursive evaluator, exceptions as control flow
  def eval(e: Expr): BigInt = {
    decreases(e)
    e match {
      case Lit(v) => v
      case Neg(e) => -eval(e)
      case Div(l, r) =>
        val lv = eval(l)
        val rv = eval(r)
        if (rv == 0) throw DivByZero()
        lv / rv
    }
  }.throwing {
    case DivByZero() => !noDiv(e)
    case _ => false
  }

  def noDiv(e: Expr): Boolean = {
    decreases(e)
    e match {
      case Lit(_) => true
      case Neg(e) => noDiv(e)
      case Div(_, _) => false
    }
  }

  def evalPure(e: Expr): BigInt = {
    require(noDiv(e))
    eval(e)
  }

  def evalOr(e: Expr, default: BigInt): BigInt = {
    try eval(e) catch {
      case _: EvalError => default
    }
  }

  // Generic throwing function
  def head[T](l: List[T]): T = {
    l match {
      case Cons(h, _) => h
      case Nil() => throw Other(0)
    }
  }.throwing {
    case Other(c) => c == 0 && l == Nil[T]()
    case _ => false
  }

  def headOr[T](l: List[T], d: T): T = try head(l) catch { case Other(_) => d }

  // Local throwing function
  def local(x: BigInt): BigInt = {
    def inner(y: BigInt): BigInt = {
      if (y < 0) throw Other(y)
      y
    }.throwing { case Other(c) => c < 0; case _ => false }

    try inner(x) + inner(x + 1) catch { case Other(c) => c }
  }.ensuring(res => res >= -1 || x < -1)

  // Nested try and rethrow
  def nested(x: BigInt): BigInt = {
    try {
      try {
        if (x < 0) throw Other(x)
        if (x == 0) throw DivByZero()
        x
      } catch {
        case Other(c) => throw TypeError("neg")
      }
    } catch {
      case TypeError(_) => BigInt(-1)
      case DivByZero() => BigInt(0)
    }
  }.ensuring(res => res >= -1)


  // An exception may not escape a lambda
  def inLambda(l: List[BigInt]): List[BigInt] = {
    l.map(x => head(List(x)) + headOr(List[BigInt](), x))
  }

  // Return in a try with finally
  def retFinally(x: BigInt): BigInt = {
    var c: BigInt = 0
    try {
      if (x > 0) return x
      c = c + 1
    } finally {
      c = c + 10
    }
    c
  }.ensuring(res => res > 0)

  @extern
  def ext(x: BigInt): BigInt = {
    x
  }.throwing { case _: EvalError => true; case _ => false }

  def useExt(x: BigInt): BigInt = try ext(x) catch { case _: EvalError => BigInt(0) }
}
