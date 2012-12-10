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

import CodeGeneration._

class CompilationUnit(val program: Program, val classes: Map[Definition, ClassFile], implicit val env: CompilationEnvironment) {

  val jvmClassToDef = classes.map{ case (d, cf) => cf.className -> d }.toMap

  val loader = new CafebabeClassLoader
  classes.values.foreach(loader.register(_))

  def writeClassFiles() {
    for ((d, cl) <- classes) {
      cl.writeToFile(cl.className + ".class")
    }
  }

  private var _nextExprId = 0
  def nextExprId = {
    _nextExprId += 1
    _nextExprId
  }

  private[codegen] def groundExprToJava(e: Expr): Any = {
    compileExpression(e, Seq()).evalToJava(Seq())
  }

  private[codegen] def javaToGroundExpr(e: AnyRef): Expr = e match {
    case i: Integer =>
      IntLiteral(i.toInt)

    case b: java.lang.Boolean =>
      BooleanLiteral(b.booleanValue)

    case cc: runtime.CaseClass =>
      val fields = cc.productElements()

      jvmClassToDef.get(e.getClass.getName) match {
        case Some(cc: CaseClassDef) =>
          CaseClass(cc, fields.map(javaToGroundExpr))
        case _ =>
          throw CompilationException("Unsupported return value : " + e)
      }

    case tpl: runtime.Tuple =>
      val elems = for (i <- 0 until tpl.getArity) yield {
        javaToGroundExpr(tpl.get(i))
      }

      Tuple(elems)

    case _ => 
      throw CompilationException("MEH Unsupported return value : " + e.getClass)
  }

  def compileExpression(e: Expr, args: Seq[Identifier]): CompiledExpression = {

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

      case UnitType | TupleType(_)  | SetType(_) | MapType(_, _) | AbstractClassType(_) | CaseClassType(_) => 
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze

    loader.register(cf)

    new CompiledExpression(this, cf, args)
  }
}

object CompilationUnit {
  def compileProgram(p: Program): Option[CompilationUnit] = {
    implicit val env = CompilationEnvironment.fromProgram(p)

    var classes = Map[Definition, ClassFile]()

    for((parent,children) <- p.algebraicDataTypes) {
      classes += parent -> compileAbstractClassDef(p, parent)

      for (c <- children) {
        classes += c -> compileCaseClassDef(p, c)
      }
    } 

    val mainClassName = defToJVMName(p, p.mainObject)
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
