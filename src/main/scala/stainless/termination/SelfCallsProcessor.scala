/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._

class SelfCallsProcessor(val checker: TerminationChecker) extends Processor {

  val name: String = "Self Calls Processor"

  def run(problem: Problem): Option[Seq[Result]] = {
    reporter.debug("- Self calls processor...")
    
    val nonTerminating = problem.funDefs
      .filter(fd => fd.hasBody && alwaysCalls(fd.body.get, fd))
    
    if (nonTerminating.nonEmpty)
      Some(nonTerminating.map(fd => Broken(fd, Seq(Variable(FreshIdentifier("any input"))))))
    else
      None
  }
  
  
  def alwaysCalls(expr: Expr, f: FunDef): Boolean = {
    val seenFunDefs = collection.mutable.HashSet[FunDef]()
    
    def rec(e0: Expr): Boolean = e0 match {
      case Assert(pred: Expr, error: Option[String], body: Expr) => rec(pred) || rec(body)
      case Let(binder: Identifier, value: Expr, body: Expr) => rec(value) || rec(body)
      case LetDef(fds, body: Expr) => rec(body) // don't enter fds because we don't know if it will be called
      case FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) =>
        tfd.fd == f /* <-- success in proving non-termination */ ||
        args.exists(arg => rec(arg)) || (tfd.fd.hasBody && (!seenFunDefs.contains(tfd.fd)) && {
          seenFunDefs += tfd.fd
          rec(tfd.fd.body.get)
        })
      case Application(caller: Expr, args: Seq[Expr]) => rec(caller) || args.exists(arg => rec(arg))
      case Lambda(args: Seq[ValDef], body: Expr) => false // we don't know if it will be called
      //case Forall(args: Seq[ValDef], body: Expr) ?
      case IfExpr(cond: Expr, thenn: Expr, elze: Expr) => rec(cond) // don't enter thenn/elze
      case Tuple (exprs: Seq[Expr]) => exprs.exists(ex => rec(ex))
      case TupleSelect(tuple: Expr, index: Int) => rec(tuple)
      case MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) => rec(scrutinee)
      // case Passes(in: Expr, out : Expr, cases : Seq[MatchCase]) ?
      case And(exprs: Seq[Expr]) => rec(exprs.head) // only the first expr will definitely be executed, if it returns false,
         // nothing more will be executed due to short-curcuit evaluation
      case Or(exprs: Seq[Expr]) => rec(exprs.head)
      // case Implies(lhs: Expr, rhs: Expr) short-circuit evaluation as well?
      case Not(expr: Expr) => rec(expr)
      case Equals(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case CaseClass(ct, args: Seq[Expr]) => args.exists(arg => rec(arg)) 
      case IsInstanceOf(expr: Expr, ct) => rec(expr)
      case AsInstanceOf(expr: Expr, ct) => rec(expr)
      case CaseClassSelector(ct, caseClassExpr, selector) => rec(caseClassExpr)
      case Plus(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case Minus(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case UMinus(expr: Expr) => rec(expr) 
      case Times(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs) 
      case Division(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs) 
      case Modulo(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case LessThan(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case GreaterThan(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case LessEquals(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      case GreaterEquals(lhs: Expr, rhs: Expr) => rec(lhs) || rec(rhs)
      /* TODO marker trait for Bit-vector arithmetic and treat them all at once */
      // TODO set & map operations
      case _ => false
    }
    
    rec(expr)
  }
}
