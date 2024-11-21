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

  private def isTailRecursive(fd: FunDef): Boolean = {
    var functionRefs = mutable.ListBuffer.empty[FunDef]
    val functionRefVisitor = new ir.Visitor(SIR) {
      override protected def visit(expr: Expr): Unit = expr match {
        case FunVal(fd) => functionRefs += fd
        case _ =>
      }
    }
    var tailFunctionRefs = mutable.ListBuffer.empty[FunDef]
    val tailRecCallVisitor = new ir.Visitor(SIR) {
      override protected def visit(expr: Expr): Unit = expr match {
        case Return(App(FunVal(fdcall), _, _)) => tailFunctionRefs += fdcall
        case _ =>
      }
    }
    functionRefVisitor(fd)
    tailRecCallVisitor(fd)
    functionRefs.contains(fd) && functionRefs.filter(_ == fd).size == tailFunctionRefs.filter(_ == fd).size
  }

  override protected def recImpl(fd: SIR.FunDef)(using Unit): to.FunDef = {
    if isTailRecursive(fd) then
      pprint.pprintln(fd)
      fd.asInstanceOf[TIR.FunDef]
    else fd.asInstanceOf[TIR.FunDef]
  }
}
