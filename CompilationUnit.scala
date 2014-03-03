/* Copyright 2009-2013 EPFL, Lausanne */

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

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor

class CompilationUnit(val ctx: LeonContext,
                      val program: Program,
                      val params: CodeGenParams = CodeGenParams()) extends CodeGeneration {

  val loader = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)

  var classes     = Map[Definition, ClassFile]()
  var defToModule = Map[Definition, ModuleDef]()

  def defineClass(df: Definition) {
    val cName = defToJVMName(df)

    val cf = df match {
      case ccd: CaseClassDef =>
        val pName = ccd.parent.map(parent => defToJVMName(parent.classDef))
        new ClassFile(cName, pName)

      case acd: AbstractClassDef =>
        new ClassFile(cName, None)

      case ob: ModuleDef =>
        new ClassFile(cName, None)

      case _ =>
        sys.error("Unhandled definition type")
    }

    classes += df -> cf
  }

  def jvmClassToLeonClass(name: String): Option[Definition] = {
    classes.find(_._2.className == name).map(_._1)
  }

  def leonClassToJVMInfo(cd: ClassDef): Option[(String, String)] = {
    classes.get(cd) match {
      case Some(cf) =>
        val sig = "(" + cd.fields.map(f => typeToJVM(f.tpe)).mkString("") + ")V"
        Some((cf.className, sig))
      case _ => None
    }
  }

  // Returns className, methodName, methodSignature
  private[this] var funDefInfo = Map[FunDef, (String, String, String)]()

  def leonFunDefToJVMInfo(fd: FunDef): Option[(String, String, String)] = {
    funDefInfo.get(fd).orElse {
      val monitorType = if (params.requireMonitor) "L"+MonitorClass+";" else ""

      val sig = "(" + monitorType + fd.params.map(a => typeToJVM(a.tpe)).mkString("") + ")" + typeToJVM(fd.returnType)

      defToModule.get(fd).flatMap(m => classes.get(m)) match {
        case Some(cf) =>
          val res = (cf.className, idToSafeJVMName(fd.id), sig)
          funDefInfo += fd -> res
          Some(res)
        case None =>
          None
      }
    }
  }

  // Get the Java constructor corresponding to the Case class
  private[this] var ccdConstructors = Map[CaseClassDef, Constructor[_]]()

  private[this] def caseClassConstructor(ccd: CaseClassDef): Option[Constructor[_]] = {
    ccdConstructors.get(ccd).orElse {
      classes.get(ccd) match {
        case Some(cf) =>
          val klass = loader.loadClass(cf.className)
          // This is a hack: we pick the constructor with the most arguments.
          val conss = klass.getConstructors().sortBy(_.getParameterTypes().length)
          assert(!conss.isEmpty)
          val cons = conss.last

          ccdConstructors += ccd -> cons
          Some(cons)
        case None =>
          None
      }
    }
  }

  private[this] lazy val tupleConstructor: Constructor[_] = {
    val tc = loader.loadClass("leon.codegen.runtime.Tuple")
    val conss = tc.getConstructors().sortBy(_.getParameterTypes().length)
    assert(!conss.isEmpty)
    conss.last
  }

  // Currently, this method is only used to prepare arguments to reflective calls.
  // This means it is safe to return AnyRef (as opposed to primitive types), because
  // reflection needs this anyway.
  private[codegen] def exprToJVM(e: Expr): AnyRef = e match {
    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case GenericValue(tp, id) =>
      e

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(exprToJVM).toArray).asInstanceOf[AnyRef]

    case CaseClass(cct, args) =>
      caseClassConstructor(cct.classDef) match {
        case Some(cons) =>
          cons.newInstance(args.map(exprToJVM).toArray : _*).asInstanceOf[AnyRef]
        case None =>
          ctx.reporter.fatalError("Case class constructor not found?!?")
      }

    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType) =>
      exprs.map(e => exprToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray

    // Just slightly overkill...
    case _ =>
      compileExpression(e, Seq()).evalToJVM(Seq())
  }

  // Note that this may produce untyped expressions! (typically: sets, maps)
  private[codegen] def jvmToExpr(e: AnyRef): Expr = e match {
    case i: Integer =>
      IntLiteral(i.toInt)

    case b: java.lang.Boolean =>
      BooleanLiteral(b.booleanValue)

    case cc: runtime.CaseClass =>
      val fields = cc.productElements()

      jvmClassToLeonClass(e.getClass.getName) match {
        case Some(cc: CaseClassDef) =>
          CaseClass(CaseClassType(cc, Nil), fields.map(jvmToExpr))
        case _ =>
          throw CompilationException("Unsupported return value : " + e)
      }

    case tpl: runtime.Tuple =>
      val elems = for (i <- 0 until tpl.getArity) yield {
        jvmToExpr(tpl.get(i))
      }
      Tuple(elems)

    case gv : GenericValue =>
      gv

    case set : runtime.Set =>
      FiniteSet(set.getElements().asScala.map(jvmToExpr).toSeq)

    case map : runtime.Map =>
      val pairs = map.getElements().asScala.map { entry =>
        val k = jvmToExpr(entry.getKey())
        val v = jvmToExpr(entry.getValue())
        (k, v)
      }
      FiniteMap(pairs.toSeq)

    case _ =>
      throw CompilationException("Unsupported return value : " + e.getClass)
  }

  def compileExpression(e: Expr, args: Seq[Identifier]): CompiledExpression = {
    if(e.getType == Untyped) {
      throw new IllegalArgumentException("Cannot compile untyped expression [%s].".format(e))
    }

    val id = CompilationUnit.nextExprId

    val cName = "Leon$CodeGen$Expr$"+id

    val cf = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    val argsTypes = args.map(a => typeToJVM(a.getType))

    val realArgs = if (params.requireMonitor) {
      ("L" + MonitorClass + ";") +: argsTypes
    } else {
      argsTypes
    }

    val m = cf.addMethod(
      typeToJVM(e.getType),
      "eval",
      realArgs : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val newMapping = if (params.requireMonitor) {
        args.zipWithIndex.toMap.mapValues(_ + 1)
      } else {
        args.zipWithIndex.toMap
      }

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(e)

    mkExpr(e, ch)(Locals(newMapping))

    e.getType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case UnitType | _: TupleType  | _: SetType | _: MapType | _: AbstractClassType | _: CaseClassType | _: ArrayType | _: TypeParameter =>
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze

    loader.register(cf)

    new CompiledExpression(this, cf, e, args)
  }

  def compileModule(module: ModuleDef) {
    val cf = classes(module)

    cf.addDefaultConstructor

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    for(funDef <- module.definedFunctions;
        (_,mn,_) <- leonFunDefToJVMInfo(funDef)) {

      val paramsTypes = funDef.params.map(a => typeToJVM(a.tpe))

      val realParams = if (params.requireMonitor) {
        ("L" + MonitorClass + ";") +: paramsTypes
      } else {
        paramsTypes
      }

      val m = cf.addMethod(
        typeToJVM(funDef.returnType),
        mn,
        realParams : _*
      )
      m.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL |
        METHOD_ACC_STATIC
      ).asInstanceOf[U2])

      compileFunDef(funDef, m.codeHandler)
    }
  }


  def init() {
    // First define all classes
    for (m <- program.modules) {
      for ((parent, children) <- m.algebraicDataTypes) {
        defineClass(parent)

        for (c <- children) {
          defineClass(c)
        }
      }

      for(single <- m.singleCaseClasses) {
        defineClass(single)
      }

      defineClass(m)
    }
  }

  def compile() {
    // Compile everything
    for (m <- program.modules) {
      for ((parent, children) <- m.algebraicDataTypes) {
        compileAbstractClassDef(parent)

        for (c <- children) {
          compileCaseClassDef(c)
        }
      }

      for(single <- m.singleCaseClasses) {
        compileCaseClassDef(single)
      }

      for(funDef <- m.definedFunctions) {
        defToModule += funDef -> m
      }
    }

    for (m <- program.modules) {
      compileModule(m)
    }

    classes.values.foreach(loader.register _)
  }

  def writeClassFiles() {
    for ((d, cl) <- classes) {
      cl.writeToFile(cl.className + ".class")
    }
  }

  init()
  compile()
}

object CompilationUnit {
  private var _nextExprId = 0
  private def nextExprId = synchronized {
    _nextExprId += 1
    _nextExprId
  }
}

