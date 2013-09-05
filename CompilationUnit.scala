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

import CodeGeneration._

class CompilationUnit(val program: Program, val classes: Map[Definition, ClassFile], implicit val env: CompilationEnvironment) {

  val jvmClassToDef = classes.map {
    case (d, cf) => cf.className -> d
  }.toMap

  protected[codegen] val loader = {
    val l = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)
    classes.values.foreach(l.register(_))
    l
  }

  private val caseClassConstructors : Map[CaseClassDef,Constructor[_]] = {
    (classes collect {
      case (ccd : CaseClassDef, cf) =>
        val klass = loader.loadClass(cf.className)
        // This is a hack: we pick the constructor with the most arguments.
        val conss = klass.getConstructors().sortBy(_.getParameterTypes().length)
        assert(!conss.isEmpty)
        (ccd -> conss.last)
    }).toMap
  }

  private lazy val tupleConstructor: Constructor[_] = {
    val tc = loader.loadClass("leon.codegen.runtime.Tuple")
    val conss = tc.getConstructors().sortBy(_.getParameterTypes().length)
    assert(!conss.isEmpty)
    conss.last
  }

  private def writeClassFiles() {
    for ((d, cl) <- classes) {
      cl.writeToFile(cl.className + ".class")
    }
  }

  private var _nextExprId = 0
  private def nextExprId = {
    _nextExprId += 1
    _nextExprId
  }

  // Currently, this method is only used to prepare arguments to reflective calls.
  // This means it is safe to return AnyRef (as opposed to primitive types), because
  // reflection needs this anyway.
  private[codegen] def valueToJVM(e: Expr): AnyRef = e match {
    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(valueToJVM).toArray).asInstanceOf[AnyRef]

    case CaseClass(ccd, args) =>
      val cons = caseClassConstructors(ccd)
      cons.newInstance(args.map(valueToJVM).toArray : _*).asInstanceOf[AnyRef]

    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType) =>
      exprs.map(e => valueToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray

    // Just slightly overkill...
    case _ =>
      compileExpression(e, Seq()).evalToJVM(Seq())
  }

  // Note that this may produce untyped expressions! (typically: sets, maps)
  private[codegen] def jvmToValue(e: AnyRef): Expr = e match {
    case i: Integer =>
      IntLiteral(i.toInt)

    case b: java.lang.Boolean =>
      BooleanLiteral(b.booleanValue)

    case cc: runtime.CaseClass =>
      val fields = cc.productElements()

      jvmClassToDef.get(e.getClass.getName) match {
        case Some(cc: CaseClassDef) =>
          CaseClass(cc, fields.map(jvmToValue))
        case _ =>
          throw CompilationException("Unsupported return value : " + e)
      }

    case tpl: runtime.Tuple =>
      val elems = for (i <- 0 until tpl.getArity) yield {
        jvmToValue(tpl.get(i))
      }
      Tuple(elems)

    case set : runtime.Set =>
      FiniteSet(set.getElements().asScala.map(jvmToValue).toSeq)

    case map : runtime.Map =>
      val pairs = map.getElements().asScala.map { entry =>
        val k = jvmToValue(entry.getKey())
        val v = jvmToValue(entry.getValue())
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

    val id = nextExprId

    val cName = "Leon$CodeGen$Expr$"+id

    val cf = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    val m = cf.addMethod(
      typeToJVM(e.getType),
      "eval",
      args.map(a => typeToJVM(a.getType)) : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val newMapping    = args.zipWithIndex.toMap

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(e)

    mkExpr(e, ch)(env.withVars(newMapping))

    e.getType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case UnitType | _: TupleType  | _: SetType | _: MapType | _: AbstractClassType | _: CaseClassType | _: ArrayType =>
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze

    loader.register(cf)

    new CompiledExpression(this, cf, e, args)
  }

  // writeClassFiles
}

object CompilationUnit {
  def compileProgram(p: Program, compileContracts: Boolean = true): Option[CompilationUnit] = {
    implicit val env = CompilationEnvironment.fromProgram(p, compileContracts)

    var classes = Map[Definition, ClassFile]()

    for((parent,children) <- p.algebraicDataTypes) {
      classes += parent -> compileAbstractClassDef(parent)

      for (c <- children) {
        classes += c -> compileCaseClassDef(c)
      }
    }

    for(single <- p.singleCaseClasses) {
      classes += single -> compileCaseClassDef(single)
    }

    val mainClassName = defToJVMName(p.mainObject)
    val cf = new ClassFile(mainClassName, None)

    classes += p.mainObject -> cf

    cf.addDefaultConstructor

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    // This assumes that all functions of a given program get compiled
    // as methods of a single class file.
    for(funDef <- p.definedFunctions;
        (_,mn,_) <- env.funDefToMethod(funDef)) {

      val m = cf.addMethod(
        typeToJVM(funDef.returnType),
        mn,
        funDef.args.map(a => typeToJVM(a.tpe)) : _*
      )
      m.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL |
        METHOD_ACC_STATIC
      ).asInstanceOf[U2])

      compileFunDef(funDef, m.codeHandler)
    }

    Some(new CompilationUnit(p, classes, env))
  }
}
