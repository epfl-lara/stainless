package leon
package codegen

import purescala.Common._
import purescala.Definitions._

import cafebabe._
import cafebabe.ClassFileTypes.U2
import cafebabe.Flags._

object CodeGenPhase extends LeonPhase[Program,CompilationResult] {
  val name = "CodeGen"
  val description = "Compiles a Leon program into Java methods"

  def run(ctx : LeonContext)(p : Program) : CompilationResult = {
    import CodeGeneration._

    // This sets up an environment where all classes and all functions have names.
    implicit val env = CompilationEnvironment.fromProgram(p)

    for((parent,children) <- p.algebraicDataTypes) {
      val acf = compileAbstractClassDef(p, parent)
      val ccfs = children.map(c => compileCaseClassDef(p, c))
    } 

    val mainClassName = defToJVMName(p, p.mainObject)
    val cf = new ClassFile(mainClassName, None)
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
 
      CodeGeneration.compileFunDef(funDef, m.codeHandler)
    }

    cf.writeToFile(mainClassName + ".class")

    CompilationResult(successful = true)
  } 
}
