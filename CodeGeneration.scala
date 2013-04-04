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
  private val BoxedIntClass  = "java/lang/Integer"
  private val BoxedBoolClass = "java/lang/Boolean"

  private val TupleClass     = "leon/codegen/runtime/Tuple"
  private val SetClass       = "leon/codegen/runtime/Set"
  private val MapClass       = "leon/codegen/runtime/Map"
  private val CaseClassClass = "leon/codegen/runtime/CaseClass"
  private val ErrorClass     = "leon/codegen/runtime/LeonCodeGenRuntimeException"
  private val ImpossibleEvaluationClass = "leon/codegen/runtime/LeonCodeGenEvaluationException"

  def defToJVMName(p : Program, d : Definition) : String = "Leon$CodeGen$" + d.id.uniqueName

  def typeToJVM(tpe : TypeTree)(implicit env : CompilationEnvironment) : String = tpe match {
    case Int32Type => "I"

    case BooleanType => "Z"

    case UnitType => "Z"

    case c : ClassType =>
      env.classDefToClass(c.classDef).map(n => "L" + n + ";").getOrElse("Unsupported class " + c.id)

    case _ : TupleType =>
      "L" + TupleClass + ";"

    case _ : SetType =>
      "L" + SetClass + ";"

    case _ : MapType =>
      "L" + MapClass + ";"

    case ArrayType(base) =>
      "[" + typeToJVM(base)

    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  // Assumes the CodeHandler has never received any bytecode.
  // Generates method body, and freezes the handler at the end.
  def compileFunDef(funDef : FunDef, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    val newMapping = funDef.args.map(_.id).zipWithIndex.toMap

    val bodyWithPre = if(funDef.hasPrecondition) {
      IfExpr(funDef.precondition.get, funDef.getBody, Error("Precondition failed"))
    } else {
      funDef.getBody
    }

    val bodyWithPost = if(funDef.hasPostcondition) {
      val freshResID = FreshIdentifier("result").setType(funDef.returnType)
      val post = purescala.TreeOps.replace(Map(ResultVariable() -> Variable(freshResID)), funDef.postcondition.get)
      Let(freshResID, bodyWithPre, IfExpr(post, Variable(freshResID), Error("Postcondition failed")) )
    } else {
      bodyWithPre
    }

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(bodyWithPost)

    mkExpr(exprToCompile, ch)(env.withVars(newMapping))

    funDef.returnType match {
      case Int32Type | BooleanType | UnitType =>
        ch << IRETURN

      case _ : ClassType | _ : TupleType | _ : SetType | _ : MapType | _ : ArrayType =>
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other.getClass)
    }

    ch.freeze
  }

  private[codegen] def mkExpr(e : Expr, ch : CodeHandler, canDelegateToMkBranch : Boolean = true)(implicit env : CompilationEnvironment) {
    e match {
      case Variable(id) =>
        val slot = slotFor(id)
        val instr = id.getType match {
          case Int32Type | BooleanType | UnitType => ILoad(slot)
          case _ => ALoad(slot)
        }
        ch << instr

      case Let(i,d,b) =>
        mkExpr(d, ch)
        val slot = ch.getFreshVar
        val instr = i.getType match {
          case Int32Type | BooleanType | UnitType => IStore(slot)
          case _ => AStore(slot)
        }
        ch << instr
        mkExpr(b, ch)(env.withVars(Map(i -> slot)))

      case LetTuple(is,d,b) =>
        mkExpr(d, ch) // the tuple
        var count = 0
        val withSlots = is.map(i => (i, ch.getFreshVar))
        for((i,s) <- withSlots) {
          ch << DUP
          ch << Ldc(count)
          ch << InvokeVirtual(TupleClass, "get", "(I)Ljava/lang/Object;")
          mkUnbox(i.getType, ch)
          val instr = i.getType match {
            case Int32Type | BooleanType | UnitType => IStore(s)
            case _ => AStore(s)
          }
          ch << instr
          count += 1
        }
        mkExpr(b, ch)(env.withVars(withSlots.toMap))

      case IntLiteral(v) =>
        ch << Ldc(v)

      case BooleanLiteral(v) =>
        ch << Ldc(if(v) 1 else 0)

      case UnitLiteral =>
        ch << Ldc(1)

      // Case classes
      case CaseClass(ccd, as) =>
        val ccName = env.classDefToClass(ccd).getOrElse {
          throw CompilationException("Unknown class : " + ccd.id)
        }
        // TODO FIXME It's a little ugly that we do it each time. Could be in env.
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

      // Tuples (note that instanceOf checks are in mkBranch)
      case Tuple(es) =>
        ch << New(TupleClass) << DUP
        ch << Ldc(es.size)
        ch << NewArray("java/lang/Object")
        for((e,i) <- es.zipWithIndex) {
          ch << DUP
          ch << Ldc(i)
          mkBoxedExpr(e, ch)
          ch << AASTORE
        }
        ch << InvokeSpecial(TupleClass, constructorName, "([Ljava/lang/Object;)V")

      case TupleSelect(t, i) =>
        val TupleType(bs) = t.getType
        mkExpr(t,ch)
        ch << Ldc(i - 1)
        ch << InvokeVirtual(TupleClass, "get", "(I)Ljava/lang/Object;")
        mkUnbox(bs(i - 1), ch)

      // Sets
      case FiniteSet(es) =>
        ch << DefaultNew(SetClass)
        for(e <- es) {
          ch << DUP
          mkBoxedExpr(e, ch)
          ch << InvokeVirtual(SetClass, "add", "(Ljava/lang/Object;)V")
        }

      case ElementOfSet(e, s) =>
        mkExpr(s, ch)
        mkBoxedExpr(e, ch)
        ch << InvokeVirtual(SetClass, "contains", "(Ljava/lang/Object;)Z")

      case SetCardinality(s) =>
        mkExpr(s, ch)
        ch << InvokeVirtual(SetClass, "size", "()I")

      case SubsetOf(s1, s2) =>
        mkExpr(s1, ch)
        mkExpr(s2, ch)
        ch << InvokeVirtual(SetClass, "subsetOf", "(L%s;)Z".format(SetClass))

      case SetIntersection(s1, s2) =>
        mkExpr(s1, ch)
        mkExpr(s2, ch)
        ch << InvokeVirtual(SetClass, "intersect", "(L%s;)L%s;".format(SetClass,SetClass))

      case SetUnion(s1, s2) =>
        mkExpr(s1, ch)
        mkExpr(s2, ch)
        ch << InvokeVirtual(SetClass, "union", "(L%s;)L%s;".format(SetClass,SetClass))

      case SetDifference(s1, s2) =>
        mkExpr(s1, ch)
        mkExpr(s2, ch)
        ch << InvokeVirtual(SetClass, "minus", "(L%s;)L%s;".format(SetClass,SetClass))

      // Maps
      case FiniteMap(ss) =>
        ch << DefaultNew(MapClass)
        for((f,t) <- ss) {
          ch << DUP
          mkBoxedExpr(f, ch)
          mkBoxedExpr(t, ch)
          ch << InvokeVirtual(MapClass, "add", "(Ljava/lang/Object;Ljava/lang/Object;)V")
        }

      case MapGet(m, k) =>
        val MapType(_, tt) = m.getType
        mkExpr(m, ch)
        mkBoxedExpr(k, ch)
        ch << InvokeVirtual(MapClass, "get", "(Ljava/lang/Object;)Ljava/lang/Object;")
        mkUnbox(tt, ch)

      case MapIsDefinedAt(m, k) =>
        mkExpr(m, ch)
        mkBoxedExpr(k, ch)
        ch << InvokeVirtual(MapClass, "isDefinedAt", "(Ljava/lang/Object;)Z")

      case MapUnion(m1, m2) =>
        mkExpr(m1, ch)
        mkExpr(m2, ch)
        ch << InvokeVirtual(MapClass, "union", "(L%s;)L%s;".format(MapClass,MapClass))

      // Branching
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

      // Arithmetic
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

      case Division(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IDIV

      case Modulo(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IREM

      case UMinus(e) =>
        mkExpr(e, ch)
        ch << INEG

      case ArrayLength(a) =>
        mkExpr(a, ch)
        ch << ARRAYLENGTH

      case as @ ArraySelect(a,i) =>
        mkExpr(a, ch)
        mkExpr(i, ch)
        ch << (as.getType match {
          case Untyped => throw CompilationException("Cannot compile untyped array access.")
          case Int32Type => IALOAD
          case BooleanType => BALOAD
          case _ => AALOAD
        })

      case a @ FiniteArray(es) =>
        ch << Ldc(es.size)
        val storeInstr = a.getType match {
          case ArrayType(Int32Type) => ch << NewArray.primitive("T_INT"); IASTORE
          case ArrayType(BooleanType) => ch << NewArray.primitive("T_BOOLEAN"); BASTORE
          case ArrayType(other) => ch << NewArray(typeToJVM(other)); AASTORE
          case other => throw CompilationException("Cannot compile finite array expression whose type is %s.".format(other))
        }
        for((e,i) <- es.zipWithIndex) {
          ch << DUP << Ldc(i)
          mkExpr(e, ch) 
          ch << storeInstr
        }

      // Misc and boolean tests
      case Error(desc) =>
        ch << New(ErrorClass) << DUP
        ch << Ldc(desc)
        ch << InvokeSpecial(ErrorClass, constructorName, "(Ljava/lang/String;)V")
        ch << ATHROW

      case Choose(_, _) =>
        ch << New(ImpossibleEvaluationClass) << DUP
        ch << Ldc("Cannot execute choose.")
        ch << InvokeSpecial(ImpossibleEvaluationClass, constructorName, "(Ljava/lang/String;)V")
        ch << ATHROW

      case b if b.getType == BooleanType && canDelegateToMkBranch =>
        val fl = ch.getFreshLabel("boolfalse")
        val al = ch.getFreshLabel("boolafter")
        ch << Ldc(1)
        mkBranch(b, al, fl, ch, canDelegateToMkExpr = false)
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

      case BooleanType | UnitType =>
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

      case BooleanType | UnitType =>
        ch << New(BoxedBoolClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

      case _ => 
    }
  }

  // Assumes that the top of the stack contains a value that should be of type `tpe`, and unboxes it to the right (JVM) type.
  private[codegen] def mkUnbox(tpe : TypeTree, ch : CodeHandler)(implicit env : CompilationEnvironment) {
    tpe match {
      case Int32Type =>
        ch << CheckCast(BoxedIntClass) << InvokeVirtual(BoxedIntClass, "intValue", "()I")

      case BooleanType | UnitType =>
        ch << CheckCast(BoxedBoolClass) << InvokeVirtual(BoxedBoolClass, "booleanValue", "()Z")

      case ct : ClassType =>
        val cn = env.classDefToClass(ct.classDef).getOrElse {
          throw new CompilationException("Unsupported class type : " + ct)
        }
        ch << CheckCast(cn)

      case tt : TupleType =>
        ch << CheckCast(TupleClass)

      case st : SetType =>
        ch << CheckCast(SetClass)

      case mt : MapType =>
        ch << CheckCast(MapClass)

      case _ =>
        throw new CompilationException("Unsupported type in unboxing : " + tpe)
    }
  }

  private[codegen] def mkBranch(cond : Expr, then : String, elze : String, ch : CodeHandler, canDelegateToMkExpr : Boolean = true)(implicit env : CompilationEnvironment) {
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

      case Implies(l, r) =>
        mkBranch(Or(Not(l), r), then, elze, ch)

      case Not(c) =>
        mkBranch(c, elze, then, ch)

      case Variable(b) =>
        ch << ILoad(slotFor(b)) << IfEq(elze) << Goto(then)

      case Equals(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        l.getType match {
          case Int32Type | BooleanType | UnitType =>
            ch << If_ICmpEq(then) << Goto(elze)

          case _ =>
            ch << InvokeVirtual("java/lang/Object", "equals", "(Ljava/lang/Object;)Z")
            ch << IfEq(elze) << Goto(then)
        }

      case Iff(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << If_ICmpEq(then) << Goto(elze)

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

      case other if canDelegateToMkExpr =>
        mkExpr(other, ch, canDelegateToMkBranch = false)
        ch << IfEq(elze) << Goto(then)

      case other => throw CompilationException("Unsupported branching expr. : " + other) 
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

    cf.addInterface(CaseClassClass)

    cf.addDefaultConstructor

    cf
  }

  def compileCaseClassDef(p : Program, ccd : CaseClassDef)(implicit env : CompilationEnvironment) : ClassFile = {

    val cName = defToJVMName(p, ccd)
    val pName = ccd.parent.map(parent => defToJVMName(p, parent))

    val cf = new ClassFile(cName, pName)
    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    if(ccd.parent.isEmpty) {
      cf.addInterface(CaseClassClass)
    }

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

      cch << ALoad(0)
      cch << InvokeSpecial(pName.getOrElse("java/lang/Object"), constructorName, "()V")

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
      val pnm = cf.addMethod("Ljava/lang/String;", "productName")
      pnm.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val pnch = pnm.codeHandler

      pnch << Ldc(cName) << ARETURN

      pnch.freeze
    }

    locally {
      val pem = cf.addMethod("[Ljava/lang/Object;", "productElements")
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
        mkBox(f.tpe, pech)
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

    cf
  }
}
