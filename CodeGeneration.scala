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
    val newMapping = funDef.args.map(_.id).zipWithIndex.toMap
    mkExpr(funDef.getBody, ch)(env.withVars(newMapping))

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
      case Variable(id) =>
        val slot = slotFor(id)
        val instr = id.getType match {
          case Int32Type | BooleanType => ILoad(slot)
          case _ => ALoad(slot)
        }
        ch << instr

      case Let(i,d,b) =>
        mkExpr(d, ch)
        val slot = ch.getFreshVar
        val instr = i.getType match {
          case Int32Type | BooleanType => IStore(slot)
          case _ => AStore(slot)
        }
        ch << instr
        mkExpr(b, ch)(env.withVars(Map(i -> slot)))

      case IntLiteral(v) =>
        ch << Ldc(v)

      case BooleanLiteral(true) =>
        ch << Ldc(1)

      case BooleanLiteral(false) =>
        ch << Ldc(0)

      case IfExpr(c, t, e) =>
        val tl = ch.getFreshLabel("then")
        val el = ch.getFreshLabel("else")
        val al = ch.getFreshLabel("after")
        mkBranch(c, tl, el, ch)
        ch << Label(tl)
        mkExpr(t, ch)
        ch << Goto(al) << Label(el)
        mkExpr(e, ch)
        ch << Label(al)

      case FunctionInvocation(fd, as) =>
        val (cn, mn, ms) = env.funDefToMethod(fd).getOrElse {
          throw CompilationException("Unknown method : " + fd.id)
        }
        for(a <- as) {
          mkExpr(a, ch)
        }
        ch << InvokeStatic(cn, mn, ms)

      case Plus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IADD

      case Minus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << ISUB

      case Times(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IMUL

      case UMinus(e) =>
        mkExpr(Minus(IntLiteral(0), e), ch)

      case _ => throw CompilationException("Unsupported expr. : " + e) 
    }
  }

  private def mkBranch(cond : Expr, then : String, elze : String, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    cond match {
      case BooleanLiteral(true) =>
        ch << Goto(then)

      case BooleanLiteral(false) =>
        ch << Goto(elze)

      case And(es) =>
        val fl = ch.getFreshLabel("andnext")
        mkBranch(es.head, fl, elze, ch)
        ch << Label(fl)
        mkBranch(And(es.tail), then, elze, ch)

      case Or(es) =>
        val fl = ch.getFreshLabel("ornext")
        mkBranch(es.head, then, fl, ch)
        ch << Label(fl)
        mkBranch(Or(es.tail), then, elze, ch) 

      case Not(c) =>
        mkBranch(c, elze, then, ch)

      case Variable(b) =>
        ch << ILoad(slotFor(b)) << IfEq(elze) << Goto(then)

      case LessThan(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << If_ICmpLt(then) << Goto(elze) 
      
      case GreaterThan(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << If_ICmpGt(then) << Goto(elze) 
      
      case LessEquals(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << If_ICmpLe(then) << Goto(elze) 
      
      case GreaterEquals(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << If_ICmpGe(then) << Goto(elze) 
      
      case _ => throw CompilationException("Unsupported cond. expr. : " + cond)
    }
  }

  private def slotFor(id : Identifier)(implicit env : CompilationEnvironment) : Int = {
    env.varToLocal(id).getOrElse {
      throw CompilationException("Unknown variable : " + id)
    }
  }
}
