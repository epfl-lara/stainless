package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

object CodeGeneration {
  def defToJVMName(p : Program, d : Definition) : String = "Leon$CodeGen$" + d.id.uniqueName

  def typeToJVM(tpe : TypeTree)(implicit env : CompilationEnvironment) : String = tpe match {
    case Int32Type => "I"

    case BooleanType => "Z"

    case c : ClassType =>
      env.classDefToName(c.classDef).map(n => "L" + n + ";").getOrElse("Unsupported class " + c.id)

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
        mkExpr(e, ch)
        ch << INEG

      case b if b.getType == BooleanType =>
        val fl = ch.getFreshLabel("boolfalse")
        val al = ch.getFreshLabel("boolafter")
        ch << Ldc(1)
        mkBranch(b, al, fl, ch)
        ch << Label(fl) << POP << Ldc(0) << Label(al)

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

  def compileAbstractClassDef(p : Program, acd : AbstractClassDef)(implicit env : CompilationEnvironment) : ClassFile = {
    val cName = defToJVMName(p, acd)

    val cf  = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_ABSTRACT
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    //cf.writeToFile(cName + ".class")
    cf
  }

  def compileCaseClassDef(p : Program, ccd : CaseClassDef)(implicit env : CompilationEnvironment) : ClassFile = {
    assert(ccd.hasParent)

    val cName = defToJVMName(p, ccd)
    val pName = defToJVMName(p, ccd.parent.get)

    val cf = new ClassFile(cName, Some(pName))
    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    if(ccd.fields.isEmpty) {
      cf.addDefaultConstructor
    } else {
      val namesTypes = ccd.fields.map { vd => (vd.id.name, typeToJVM(vd.tpe)) }

      for((nme, jvmt) <- namesTypes) {
        val fh = cf.addField(jvmt, nme)
        fh.setFlags((
          FIELD_ACC_PUBLIC |
          FIELD_ACC_FINAL
        ).asInstanceOf[U2])
      }

      val cmh = cf.addConstructor(namesTypes.map(_._2).toList).codeHandler

      cmh << ALoad(0) << InvokeSpecial(pName, cafebabe.Defaults.constructorName, "()V")

      var c = 1
      for((nme, jvmt) <- namesTypes) {
        cmh << ALoad(0)
        cmh << (jvmt match {
          case "I" | "Z" => ILoad(c)
          case _ => ALoad(c)
        })
        cmh << PutField(cName, nme, jvmt)
        c += 1
      }
      cmh << RETURN
      cmh.freeze
    }

    //cf.writeToFile(cName + ".class")
    cf
  }
}
