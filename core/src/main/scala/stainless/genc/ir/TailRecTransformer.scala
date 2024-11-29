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

  /**
   * //TODO
   * Check:
   * - no continue? replace with sth? do we even need it?
   */

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

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

  /* Rewrite a tail recursive function to a while loop
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
  *    while (true) {
  *      if (n$ == 0) {
  *        return i$
  *      } else {
  *        val n$1 = n$ - 1
  *        val i$1 = j$
  *        val j$1 = i$ + j$
  *        n$ = n$1
  *        i$ = i$1
  *        j$ = j$1
  *        continue
  *      }
  *    }
  * }
  * Steps:
  * [x] Create a new variable for each parameter of the function
  * [x] Replace existing parameter references with the new variables
  * [x] Create a while loop with a condition true
  * [x] Replace the recursive return with a variable assignments (updating the state) and a continue statement
  */
  private def rewriteToAWhileLoop(fd: FunDef): FunDef = fd.body match {
    case FunBodyAST(body) =>
      val newParams = fd.params.map(p => ValDef(freshId(p.id), p.typ, isVar = true))
      val newParamMap = fd.params.zip(newParams).toMap
      val bodyWithNewParams = replaceBindings(newParamMap, body)
      val declarations = newParamMap.toList.map { case (old, nw) => Decl(nw, Some(Binding(old))) }
      val newBody = replaceRecursiveCalls(fd, bodyWithNewParams, newParams.toList)
      val newBodyWIthAWhileLoop = While(True, newBody)
      FunDef(fd.id, fd.returnType, fd.ctx, fd.params, FunBodyAST(Block(declarations :+ newBodyWIthAWhileLoop)), fd.isExported, fd.isPure)
    case _ => fd
  }

  private def replaceRecursiveCalls(fd: FunDef, body: Expr, valdefs: List[ValDef]): Expr = {
    val replacer = new Transformer(from, from) with NoEnv {
      override def rec(e: Expr)(using Env): Expr = e match {
        case Return(App(FunVal(fdcall), _, args)) if fdcall == fd =>
          val tmpValDefs = valdefs.map(vd => ValDef(freshId(vd.id), vd.typ, isVar = false))
          val tmpDecls = tmpValDefs.zip(args).map { case (vd, arg) => Decl(vd, Some(arg)) }
          val valdefAssign = valdefs.zip(tmpValDefs).map { case (vd, tmp) => Assign(Binding(vd), Binding(tmp)) }
          Block(tmpDecls ++ valdefAssign/*  :+ Continue() */)
        case _ => super.rec(e)
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

  override protected def recImpl(fd: from.FunDef)(using Unit): to.FunDef = {
    super.recImpl{
      if isTailRecursive(fd) then
        val newFd = rewriteToAWhileLoop(fd)
        pprint.pprintln(newFd)
        newFd
      else
        fd
    }
  }

  private def freshId(id: String): to.Id = id + "_" + freshCounter.next(id)

  private val freshCounter = new utils.UniqueCounter[String]()
}
