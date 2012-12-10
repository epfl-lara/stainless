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
import cafebabe.Defaults.constructorName
import cafebabe.Flags._

object CodeGeneration {
  private val BoxedIntClass = "java/lang/Integer"
  private val BoxedBoolClass = "java/lang/Boolean"

  def defToJVMName(p : Program, d : Definition) : String = "Leon$CodeGen$" + d.id.uniqueName

  def typeToJVM(tpe : TypeTree)(implicit env : CompilationEnvironment) : String = tpe match {
    case Int32Type => "I"

    case BooleanType => "Z"

    case c : ClassType =>
      env.classDefToClass(c.classDef).map(n => "L" + n + ";").getOrElse("Unsupported class " + c.id)

    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  // Assumes the CodeHandler has never received any bytecode.
  // Generates method body, and freezes the handler at the end.
  def compileFunDef(funDef : FunDef, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    val newMapping = funDef.args.map(_.id).zipWithIndex.toMap

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(funDef.getBody)

    mkExpr(exprToCompile, ch)(env.withVars(newMapping))

    funDef.returnType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze
  }

  private[codegen] def mkExpr(e : Expr, ch : CodeHandler)(implicit env : CompilationEnvironment) {
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

      case BooleanLiteral(v) =>
        ch << Ldc(if(v) 1 else 0)

      case CaseClass(ccd, as) =>
        val ccName = env.classDefToClass(ccd).getOrElse {
          throw CompilationException("Unknown class : " + ccd.id)
        }
        // It's a little ugly that we do it each time. Could be in env.
        val consSig = "(" + ccd.fields.map(f => typeToJVM(f.tpe)).mkString("") + ")V"
        ch << New(ccName) << DUP
        for(a <- as) {
          mkExpr(a, ch)
        }
        ch << InvokeSpecial(ccName, constructorName, consSig)

      case CaseClassInstanceOf(ccd, e) =>
        val ccName = env.classDefToClass(ccd).getOrElse {
          throw CompilationException("Unknown class : " + ccd.id)
        }
        mkExpr(e, ch)
        ch << InstanceOf(ccName)

      case CaseClassSelector(ccd, e, sid) =>
        mkExpr(e, ch)
        val ccName = env.classDefToClass(ccd).getOrElse {
          throw CompilationException("Unknown class : " + ccd.id)
        }
        ch << CheckCast(ccName)
        ch << GetField(ccName, sid.name, typeToJVM(sid.getType))

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

      // WARNING !!! See remark at the end of mkBranch ! The two functions are 
      // mutually recursive and will loop if none supports some Boolean construct !
      case b if b.getType == BooleanType =>
        val fl = ch.getFreshLabel("boolfalse")
        val al = ch.getFreshLabel("boolafter")
        ch << Ldc(1)
        mkBranch(b, al, fl, ch)
        ch << Label(fl) << POP << Ldc(0) << Label(al)

      case _ => throw CompilationException("Unsupported expr. : " + e) 
    }
  }

  // Leaves on the stack a value equal to `e`, always of a type compatible with java.lang.Object.
  private[codegen] def mkBoxedExpr(e : Expr, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    e.getType match {
      case Int32Type =>
        ch << New(BoxedIntClass) << DUP
        mkExpr(e, ch)
        ch << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

      case BooleanType =>
        ch << New(BoxedBoolClass) << DUP
        mkExpr(e, ch)
        ch << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

      case _ =>
        mkExpr(e, ch)
    }
  }

  // Assumes the top of the stack contains of value of the right type, and makes it
  // compatible with java.lang.Object.
  private[codegen] def mkBox(tpe : TypeTree, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    tpe match {
      case Int32Type =>
        ch << New(BoxedIntClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

      case BooleanType =>
        ch << New(BoxedBoolClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

      case _ => 
    }
  }

  // Assumes that the top of the stack contains a value that should be of type `tpe`, and unboxes it to the right (JVM) type.
  private[codegen] def mkUnbox(tpe : TypeTree, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    tpe match {
      case Int32Type =>
        ch << CheckCast(BoxedIntClass) << InvokeVirtual(BoxedIntClass, "intValue", "()I")

      case BooleanType =>
        ch << CheckCast(BoxedBoolClass) << InvokeVirtual(BoxedBoolClass, "booleanValue", "()Z")

      case ct : ClassType =>
        val cn = env.classDefToClass(ct.classDef).getOrElse {
          throw new CompilationException("Unsupported class type : " + ct)
        }
        ch << CheckCast(cn)

      case _ =>
        throw new CompilationException("Unsupported type in unboxing : " + tpe)
    }
  }

  private[codegen] def mkBranch(cond : Expr, then : String, elze : String, ch : CodeHandler)(implicit env : CompilationEnvironment) {
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

      case Equals(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        l.getType match {
          case Int32Type | BooleanType => ch << If_ICmpEq(then) << Goto(elze)
          case _ => ch << If_ACmpEq(then) << Goto(elze)
        }

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

      // WARNING !!! mkBranch delegates to mkExpr, and mkExpr delegates to mkBranch !
      // That means, between the two of them, they'd better know what to generate !
      case other =>
        mkExpr(other, ch)
        ch << IfEq(elze) << Goto(then)
    }
  }

  private[codegen] def slotFor(id : Identifier)(implicit env : CompilationEnvironment) : Int = {
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

    cf.addInterface("leon/codegen/runtime/CaseClass")

    cf.addDefaultConstructor

    cf.writeToFile(cName + ".class")
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

    // definition of the constructor
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

      val cch = cf.addConstructor(namesTypes.map(_._2).toList).codeHandler

      cch << ALoad(0) << InvokeSpecial(pName, constructorName, "()V")

      var c = 1
      for((nme, jvmt) <- namesTypes) {
        cch << ALoad(0)
        cch << (jvmt match {
          case "I" | "Z" => ILoad(c)
          case _ => ALoad(c)
        })
        cch << PutField(cName, nme, jvmt)
        c += 1
      }
      cch << RETURN
      cch.freeze
    }

    locally {
      val pem = cf.addMethod("[java/lang/Object;", "productElements")
      pem.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val pech = pem.codeHandler

      pech << Ldc(ccd.fields.size)
      pech << NewArray("java/lang/Object")

      for ((f, i) <- ccd.fields.zipWithIndex) {
        pech << DUP
        pech << Ldc(i)
        pech << ALoad(0)
        pech << GetField(cName, f.id.name, typeToJVM(f.tpe))
        pech << AASTORE
      }

      pech << ARETURN
      pech.freeze
    }

    // definition of equals
    locally {
      val emh = cf.addMethod("Z", "equals", "Ljava/lang/Object;")
      emh.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val ech = emh.codeHandler

      val notRefEq = ech.getFreshLabel("notrefeq")
      val notEq = ech.getFreshLabel("noteq")
      val castSlot = ech.getFreshVar

      // If references are equal, trees are equal.
      ech << ALoad(0) << ALoad(1) << If_ACmpNe(notRefEq) << Ldc(1) << IRETURN << Label(notRefEq)

      // We check the type (this also checks against null)....
      ech << ALoad(1) << InstanceOf(cName) << IfEq(notEq)

      // ...finally, we compare fields one by one, shortcircuiting on disequalities.
      if(!ccd.fields.isEmpty) {
        ech << ALoad(1) << CheckCast(cName) << AStore(castSlot)

        val namesTypes = ccd.fields.map { vd => (vd.id.name, typeToJVM(vd.tpe)) }
        
        for((nme, jvmt) <- namesTypes) {
          ech << ALoad(0) << GetField(cName, nme, jvmt)
          ech << ALoad(castSlot) << GetField(cName, nme, jvmt)

          jvmt match {
            case "I" | "Z" =>
              ech << If_ICmpNe(notEq)

            case ot =>
              ech << InvokeVirtual("java/lang/Object", "equals", "(Ljava/lang/Object;)Z") << IfEq(notEq)
          }
        }
      } 

      ech << Ldc(1) << IRETURN << Label(notEq) << Ldc(0) << IRETURN
      ech.freeze
    }

    // definition of hashcode
    locally {
      val hmh = cf.addMethod("I", "hashCode", "")
      hmh.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val hch = hmh.codeHandler
      // TODO FIXME. Look at Scala for inspiration.
      hch << Ldc(42) << IRETURN
      hch.freeze
    }

    cf.writeToFile(cName + ".class")
    cf
  }
}
