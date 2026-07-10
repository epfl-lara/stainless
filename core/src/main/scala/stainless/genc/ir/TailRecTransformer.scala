package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._
import scala.collection.mutable

final class TailRecTransformer(val ctx: inox.Context) extends Transformer(SIR, TIR) with NoEnv {
  import from._

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  private given printer.Context = printer.Context(0)

  /**
    * If the function returns Unit type and the last one statement is a recursive call,
    * put the recursive call in a return statement.
    * 
    * Example:
    * def countDown(n: Int): Unit =
    *   if (n == 0) return
    *   countDown(n - 1)
    * 
    * ==>
    *
    * def countDown(n: Int): Unit =
    *   if (n == 0) return
    *   return countDown(n - 1)
    */
  private def putTailRecursiveUnitCallInReturn(fd: FunDef): FunDef = {
    def go(expr: Expr): Expr = expr match {
      case Block(stmts) if stmts.nonEmpty =>
        Block(stmts.init :+ go(stmts.last))
      case IfElse(cond, thenn, elze) =>
        IfElse(cond, go(thenn), go(elze))
      case app @ App(FunVal(calledFd), _, _) if calledFd.id == fd.id =>
        Return(app)
      case _ => expr
    }
    fd.body match {
      case FunBodyAST(expr) if fd.returnType.isUnitType =>
        fd.copy(body = FunBodyAST(go(expr)))
      case _ => fd
    }
  }

  private def isTailRecursive(fd: FunDef): Boolean = {
    var functionRefs = mutable.ListBuffer.empty[FunDef]
    val functionRefVisitor = new ir.Visitor(from) {
      override protected def visit(expr: Expr): Unit = expr match {
        case FunVal(fd) => functionRefs += fd
        case _ =>
      }
    }
    var tailFunctionRefs = mutable.ListBuffer.empty[FunDef]
    val tailRecCallVisitor = new ir.Visitor(from) {
      override protected def visit(expr: Expr): Unit = expr match {
        case Return(App(FunVal(fdcall), _, _)) => tailFunctionRefs += fdcall

        case _ =>
      }
    }
    functionRefVisitor(fd)
    tailRecCallVisitor(fd)
    functionRefs.contains(fd) && functionRefs.filter(_ == fd).size == tailFunctionRefs.filter(_ == fd).size
  }

  /* Rewrite a tail recursive function to a labelled block iterated with `goto`.
  *  Example:
  *  def fib(n: Int, i: Int = 0, j: Int = 1): Int =
  *    if (n == 0)
  *      return i
  *    else
  *      return fib(n-1, j, i+j)
  *
  *  ==>
  *
  *  def fib(n: Int, i: Int = 0, j: Int = 1): Int = {
  *
  *    var n$ = n
  *    var i$ = i
  *    var j$ = j
  *    someLabel:
  *      if (n$ == 0) {
  *        return i$
  *      } else {
  *        val n$1 = n$ - 1
  *        val i$1 = j$
  *        val j$1 = i$ + j$
  *        n$ = n$1
  *        i$ = i$1
  *        j$ = j$1
  *        goto someLabel
  *      }
  * }
  * Steps:
  * - Create a new variable for each parameter of the function
  * - Replace existing parameter references with the new variables
  * - Replace the recursive return with variable assignments (updating the state) and a `goto`
  *
  * Note: no enclosing `while (true)` is needed — every path ends in either a `goto` back to
  * the label (a recursive step) or a `return` (the base case), so the backward `goto` alone
  * drives the iteration. Emitting a `while (true)` would be redundant and, worse, would turn a
  * missing base-case `return` into an infinite loop rather than a benign fall-through return.
  */
  private def rewriteToALabelledLoop(fd: FunDef): FunDef = fd.body match {
    case FunBodyAST(body) =>
      val newParams = fd.params.map(p => ValDef(freshId(p.id), p.typ, isVar = true))
      val newParamMap = fd.params.zip(newParams).toMap
      val labelName = freshId("label")
      val bodyWithNewParams = replaceBindings(newParamMap, body)
      // No terminating `return` is added on the base-case path: a Unit-returning function
      // becomes a C `void` function, and reaching the end of its body is already a normal
      // return. (Non-Unit functions have an explicit `return <value>` on every base-case path.)
      val declarations = newParamMap.toList.map { case (old, nw) => Decl(nw, Some(Binding(old))) }
      val newBody = replaceRecursiveCalls(fd, bodyWithNewParams, newParams.toList, labelName)
      val newBodyWithALabel = Labeled(labelName, newBody)
      FunDef(fd.id, fd.returnType, fd.ctx, fd.params, FunBodyAST(Block(declarations :+ newBodyWithALabel)), fd.isExported, fd.isPure)
    case _ => fd
  }

  private def replaceRecursiveCalls(fd: FunDef, body: Expr, valdefs: List[ValDef], labelName: String): Expr = {
    val replacer = new Transformer(from, from) with NoEnv {
      override def recImpl(e: Expr)(using Env): (Expr, Env) = e match {
        case Return(App(FunVal(fdcall), _, args)) if fdcall == fd && args.length == valdefs.length =>
          val tmpValDefs = valdefs.map(vd => ValDef(freshId(vd.id), vd.typ, isVar = false))
          val tmpDecls = tmpValDefs.zip(args).map { case (vd, arg) => Decl(vd, Some(arg)) }
          val valdefAssign = valdefs.zip(tmpValDefs).map { case (vd, tmp) => Assign(Binding(vd), Binding(tmp)) }
          Block(tmpDecls ++ valdefAssign :+ Goto(labelName)) -> ()
        case Return(App(FunVal(fdcall), _, _)) if fdcall == fd && fd.returnType.isUnitType =>
          Return(Lit(UnitLit)) -> ()
        case _ =>
          super.recImpl(e)
      }
    }
    replacer(body)
  }

  /* Replace the bindings in the function body with the mapped variables */
  private def replaceBindings(mapping: Map[ValDef, ValDef], funBody: Expr): Expr = {
    val replacer = new Transformer(from, from) with NoEnv {
      override protected def rec(vd: ValDef)(using Env): to.ValDef =
        mapping.getOrElse(vd, vd)
    }
    replacer(funBody)
  }

  private def replaceWithNewFuns(prog: Prog, newFdsMap: Map[FunDef, FunDef]): Prog = {
    val replacer = new Transformer(from, from) with NoEnv {
      override protected def recImpl(fd: FunDef)(using Env): FunDef =
        super.recImpl(newFdsMap.getOrElse(fd, fd))
      }
      replacer(prog)
  }

  override protected def rec(prog: from.Prog)(using Unit): to.Prog = {
    super.rec {
      val newFdsMap = prog.functions.map { fd => 
        val fdWithTailRecUnitInReturn = putTailRecursiveUnitCallInReturn(fd)
        if isTailRecursive(fdWithTailRecUnitInReturn) then
          val fdRewrittenToLoop = rewriteToALabelledLoop(fdWithTailRecUnitInReturn)
          // val irPrinter = IRPrinter(SIR)
          // print(irPrinter.apply(newFd)(using irPrinter.Context(0)))
          fd -> fdRewrittenToLoop
        else
          fd -> fdWithTailRecUnitInReturn
      }.toMap
      val newProg = Prog(prog.decls, newFdsMap.values.toSeq, prog.classes)
      replaceWithNewFuns(newProg, newFdsMap)
    }
  }

  private def freshId(id: String): to.Id = id + "_" + freshCounter.next(id)

  private val freshCounter = new utils.UniqueCounter[String]()
}
