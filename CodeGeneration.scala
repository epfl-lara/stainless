package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import cafebabe._
import cafebabe.ByteCodes._
import cafebabe.AbstractByteCodes._

object CodeGeneration {
  def programToClassName(p : Program) : String = "Leon$CodeGen$" + p.mainObject.id.uniqueName

  def typeToJVM(tpe : TypeTree)(implicit env : CompilationEnvironment) : String = tpe match {
    case Int32Type => "I"
    case BooleanType => "Z"
    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  // Assumes the CodeHandler has never received any bytecode.
  // Generates method body, and freezes the handler at the end.
  def compileFunDef(funDef : FunDef, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    // TODO, change environment to include args.
    mkExpr(funDef.getBody, ch)

    funDef.returnType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze
  }

  private def mkExpr(e : Expr, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    e match {
      case IntLiteral(v) => ch << Ldc(v)
      case BooleanLiteral(true) => ch << Ldc(1)
      case BooleanLiteral(false) => ch << Ldc(0)

      case Plus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IADD

      case Minus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << ISUB

      case UMinus(e) =>
        mkExpr(Minus(IntLiteral(0), e), ch)

      case _ => throw CompilationException("Unsupported expr : " + e) 
    }
  }
}
