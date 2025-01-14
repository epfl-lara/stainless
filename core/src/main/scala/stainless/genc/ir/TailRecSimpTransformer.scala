package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._
import scala.collection.mutable

final class TailRecSimpTransformer extends Transformer(SIR, SIR) with NoEnv {
  import from._

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  /**
    * Replace a variable assignment that is immediately 
    * returned
    * 
    * val i = f(...);
    * return i;
    * 
    * ==>
    * 
    * return f(...);
    *
    */
  private def replaceImmediateReturn(fd: Expr): Expr = {
    val transformer = new ir.Transformer(from, to) with NoEnv {
      override protected def recImpl(expr: Expr)(using Env): (Expr, Env) = expr match {
        case Block(stmts) =>
          Block(stmts.zipWithIndex.flatMap {
            case (expr @ Decl(id, Some(rhs)), idx) =>
              stmts.lift(idx + 1) match {
                case Some(Return(Binding(retId))) if retId == id =>
                  List(Return(rhs))
                case _ => List(recImpl(expr)._1)
              }
            case (expr @ Return(Binding(retId)), idx) =>
              stmts.lift(idx - 1) match {
                case Some(Decl(id, rhs)) if id == retId =>
                  Nil
                case _ => List(recImpl(expr)._1)
              }
            case (expr, idx) => List(recImpl(expr)._1)
          }) -> ()
        case expr => super.recImpl(expr)
      }
    }
    transformer(fd)
  }

  /**
    * Remove all statements after a return statement
    * 
    * return f(...);
    * someStmt;
    * 
    * ==>
    * 
    * return f(...);
    *
    */
  private def removeAfterReturn(fd: Expr): Expr = {
    val transformer = new ir.Transformer(from, to) with NoEnv {
      override protected def recImpl(expr: Expr)(using Env): (Expr, Env) = expr match {
        case Block(stmts) =>
          val transformedStmts = stmts.map(recImpl(_)._1)
          val firstReturn = transformedStmts.find {
            case Return(_) => true
            case _ => false
          }.toList
          val newStmts = transformedStmts.takeWhile {
            case Return(_) => false
            case _ => true
          }
          Block(newStmts ++ firstReturn) -> ()
        case expr => super.recImpl(expr)
      }
    }
    transformer(fd)
  }

  override protected def recImpl(fd: Expr)(using Env): (to.Expr, Env) = {
    val afterReturn = removeAfterReturn(fd)
    val immediateReturn = replaceImmediateReturn(afterReturn)
    immediateReturn -> ()
  }
}
