import stainless.lang._
import stainless.annotation._
import stainless.collection._

object IntLattice {
  sealed abstract class Element
  case class Bot() extends Element
  case class Top() extends Element
  case class BigIntVal(x: BigInt) extends Element

  def height: BigInt = {
    /**
     * A number that depends on the lattice definition.
     * In simplest case it has height 3 (_|_ (bot) <= BigInts <= T (top))
     */
    3
  }

  def join(oldVal: Element, newVal: Element) = (oldVal, newVal) match {
    case (Bot(), any) => any // bot is the identity for join
    case (any, Bot()) => any
    case (Top(), _) => Top() // top joined with anything is top
    case (_, Top()) => Top()
    case (BigIntVal(x), BigIntVal(y)) if (x == y) => BigIntVal(y)
    case _ =>
      //here old and new vals are different BigIntegers
      Top()
  }
}

object LatticeOps {
  import IntLattice._

  def add(a: Element, b: Element): Element = {
    (a, b) match {
      case (Bot(), _) => Bot()
      case (_, Bot()) => Bot()
      case (Top(), _) => Top()
      case (_, Top()) => Top()
      case (BigIntVal(x), BigIntVal(y)) => BigIntVal(x + y)
    }
  }

  def multiply(a: Element, b: Element): Element = {
    (a, b) match {
      case (_, BigIntVal(x)) if x == 0 => BigIntVal(0)
      case (BigIntVal(x), _) if x == 0 => BigIntVal(0)
      case (Bot(), _) => Bot()
      case (_, Bot()) => Bot()
      case (Top(), _) => Top()
      case (_, Top()) => Top()
      case (BigIntVal(x), BigIntVal(y)) => BigIntVal(x * y)
    }
  }
}

object ConstantPropagation {
  import IntLattice._
  import LatticeOps._

  implicit class BigIntList(val list: List[BigInt]) {
    def sum: BigInt = list match {
      case Cons(x, xs) => x + xs.sum
      case Nil() => BigInt(0)
    }
  }

  sealed abstract class Expr {
    def size: BigInt = {
      this match {
        case Plus(lhs, rhs) => 1 + lhs.size + rhs.size
        case Times(lhs, rhs) => 1 + lhs.size + rhs.size
        case FunctionCall(calleeId, args) => args.map(_.size).sum
        case IfThenElse(cond, thenExpr, elseExpr) => 1 + cond.size + thenExpr.size + elseExpr.size
        case _ => 1
      }
    }
  }

  case class Times(lhs: Expr, rhs: Expr) extends Expr
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class BigIntLiteral(v: BigInt) extends Expr
  case class FunctionCall(calleeId: BigInt, args: List[Expr]) extends Expr
  case class IfThenElse(cond: Expr, thenExpr: Expr, elseExpr: Expr) extends Expr
  case class Identifier(id: BigInt) extends Expr

  /**
   * Definition of a function AST
   */
  case class Function(id: BigInt, params: List[Expr], body: Expr)

  /**
   * Assuming that the functions are ordered from callee to
   * caller and there is no mutual recursion, only self recursion
   */
  case class Program(funcs: List[Function]) {
    def size: BigInt = funcs.map(_.body.size).sum
  }

  def size(l: List[Function]): BigInt = {
    l match {
      case Cons(_, t) => 1 + size(t)
      case Nil() => 0
    }
  }

  def initToBot(l: List[Function]): List[(BigInt /*function id*/ , Element)] = {
    l match {
      case Nil() => Nil[(BigInt /*function id*/ , Element)]()
      case Cons(fun, tail) => Cons((fun.id, Bot()), initToBot(tail))
    }
  } //ensuring (_ => steps <= ? * size(l) + ?)

  def foldConstants(p: Program): Program = {
    val initVals = initToBot(p.funcs)
    val fvals = computeSummaries(p, initToBot(p.funcs), height)
    val newfuns = transformFuns(p.funcs, fvals)
    Program(newfuns)
  } //ensuring(_ => steps <= ? * (progSize(p)*height) + ? * height + ? * size(p.funcs) + ?)

  /**
   * The initVals is the initial values for the
   * values of the functions
   */
  def computeSummaries(p: Program, initVals: List[(BigInt /*function id*/ , Element)], noIters: BigInt): List[(BigInt /*function id*/ , Element)] = {
    require(noIters >= 0)
    decreases(noIters) // FIXME(measure): Wrong measure is inferred

    if (noIters <= 0) {
      initVals
    } else
      computeSummaries(p, analyzeFuns(p.funcs, initVals, initVals), noIters - 1)
  } //ensuring(_ => steps <= ? * (progSize(p)*noIters) + ? * noIters + ?)

  /**
   * Initial fvals and oldVals are the same
   * but as the function progresses, fvals will only have the olds values
   * of the functions that are yet to be processed, whereas oldVals will remain the same.
   */
  def analyzeFuns(funcs: List[Function], fvals: List[(BigInt, Element)], oldVals: List[(BigInt, Element)]): List[(BigInt, Element)] = {
    (funcs, fvals) match {
      case (Cons(f, otherFuns), Cons((fid, fval), otherVals)) =>
        val newval = analyzeFunction(f, oldVals)
        val approxVal = join(fval, newval) //creates an approximation of newVal to ensure convergence
        Cons((fid, approxVal), analyzeFuns (otherFuns, otherVals, oldVals))
      case _ =>
        Nil[(BigInt, Element)]() //this also handles precondition violations e.g. lists aren't of same size etc.
    }
  } //ensuring (_ => steps <= ? * sizeFuncList(funcs) + ?)

  @library
  def getFunctionVal(funcId: BigInt, funcVals: List[(BigInt, Element)]): Element = {
    funcVals match {
      case Nil() => Bot()
      case Cons((currFuncId, currFuncVal), otherFuncVals) if (currFuncId == funcId) => currFuncVal
      case Cons(_, otherFuncVals) =>
        getFunctionVal(funcId, otherFuncVals)
    }
  } //ensuring (_ => steps <= 1)


  def analyzeExprList(l: List[Expr], funcVals: List[(BigInt, Element)]): List[Element] = {
    l match {
      case Nil() => Nil[Element]()
      case Cons(expr, otherExprs) => Cons(analyzeExpr(expr, funcVals), analyzeExprList(otherExprs, funcVals))
    }
  } //ensuring (_ => steps <= ? * sizeExprList(l) + ?)

  /**
   * Returns the value of the expression when "Abstractly Interpreted"
   * using the lattice.
   */
  def analyzeExpr(e: Expr, funcVals: List[(BigInt, Element)]): Element = {
    e match {
      case Times(lhs: Expr, rhs: Expr) => {
        val lval = analyzeExpr(lhs, funcVals)
        val rval = analyzeExpr(rhs, funcVals)
        multiply(lval, rval)
      }
      case Plus(lhs: Expr, rhs: Expr) => {
        val lval = analyzeExpr(lhs, funcVals)
        val rval = analyzeExpr(rhs, funcVals)
        add(lval, rval)
      }
      case FunctionCall(id, args: List[Expr]) => {
        getFunctionVal(id, funcVals)
      }
      case IfThenElse(c, th, el) => {
        //analyze then and else branches and join their values
        //TODO: this can be made more precise e.g. if 'c' is
        //a non-zero value it can only execute the then branch.
        val v1 = analyzeExpr(th, funcVals)
        val v2 = analyzeExpr(el, funcVals)
        join(v1, v2)
      }
      case lit @ BigIntLiteral(v) =>
        BigIntVal(v)

      case Identifier(_) => Bot()
    }
  } //ensuring (_ => steps <= ? * sizeExpr(e) + ?)


  def analyzeFunction(f: Function, oldVals: List[(BigInt, Element)]): Element = {
    // traverse the body of the function and simplify constants
    // for function calls assume the value given by oldVals
    // also for if-then-else statments, take a join of the values along if and else branches
    // assume that bot op any = bot and top op any = top (but this can be made more precise).
    analyzeExpr(f.body, oldVals)
  } //ensuring (_ => steps <= ? * sizeExpr(f.body) + ?)


  /**
   * Returns the folded expression
   */
  def transformExpr(e: Expr, funcVals: List[(BigInt, Element)]): Expr = {
    e match {
      case Times(lhs: Expr, rhs: Expr) => {
        val foldedLHS = transformExpr(lhs, funcVals)
        val foldedRHS = transformExpr(rhs, funcVals)
        (foldedLHS, foldedRHS) match {
          case (BigIntLiteral(x), BigIntLiteral(y)) =>
            BigIntLiteral(x * y)
          case _ =>
            Times(foldedLHS, foldedRHS)
        }
      }
      case Plus(lhs: Expr, rhs: Expr) => {
        val foldedLHS = transformExpr(lhs, funcVals)
        val foldedRHS = transformExpr(rhs, funcVals)
        (foldedLHS, foldedRHS) match {
          case (BigIntLiteral(x), BigIntLiteral(y)) =>
            BigIntLiteral(x + y)
          case _ =>
            Plus(foldedLHS, foldedRHS)
        }
      }
      case FunctionCall(calleeid, args: List[Expr]) => {
        getFunctionVal(calleeid, funcVals) match {
          case BigIntVal(x) =>
            BigIntLiteral(x)
          case _ =>
            val foldedArgs = args.map(transformExpr(_, funcVals))
            FunctionCall(calleeid, foldedArgs)
        }
      }
      case IfThenElse(c, th, el) => {
        val foldedCond = transformExpr(c, funcVals)
        val foldedTh = transformExpr(th, funcVals)
        val foldedEl = transformExpr(el, funcVals)
        foldedCond match {
          case BigIntLiteral(x) => {
            if (x != 0) foldedTh
            else foldedEl
          }
          case _ => IfThenElse(foldedCond, foldedTh, foldedEl)
        }
      }
      case _ => e
    }
  } //ensuring (_ => steps <= ? * sizeExpr(e) + ?)


  def transformFuns(funcs: List[Function], fvals: List[(BigInt, Element)]): List[Function] = {
    funcs match {
      case Cons(f, otherFuns) =>
        val newfun = Function(f.id, f.params, transformExpr(f.body, fvals))
        Cons(newfun, transformFuns(otherFuns, fvals))
      case _ =>
        Nil[Function]()
    }
  } //ensuring (_ => steps <= ? * sizeFuncList(funcs) + ?)
}
