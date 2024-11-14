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

  private def isRecursive(fd: FunDef): Boolean = {
    // var functionRefs = mutable.Set[Identifier].empty
    // val functionRefVisitor = new ir.Visitor(SIR) {
    //   override protected def visit(funRef: FunRef): Unit = {
    //     functionRefs += fi.tfd.fd.id
    //   }
    // }
    ???
  }

  override protected def recImpl(fd: SIR.FunDef)(using Unit): to.FunDef = {
    ???
  }
}
