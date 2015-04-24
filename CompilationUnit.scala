/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import purescala.Extractors._
import purescala.Constructors._
import codegen.runtime.LeonCodeGenRuntimeMonitor

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor


class CompilationUnit(val ctx: LeonContext,
                      val program: Program,
                      val params: CodeGenParams = CodeGenParams.default) extends CodeGeneration {

  val loader = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)

  var classes     = Map[Definition, ClassFile]()
  var defToModuleOrClass = Map[Definition, Definition]()
  
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
        val monitorType = if (params.requireMonitor) "L"+MonitorClass+";" else ""
        val sig = "(" + monitorType + cd.fields.map(f => typeToJVM(f.getType)).mkString("") + ")V"
        Some((cf.className, sig))
      case _ => None
    }
  }

  // Returns className, methodName, methodSignature
  private[this] var funDefInfo = Map[FunDef, (String, String, String)]()

  
  /**
   * Returns (cn, mn, sig) where 
   *  cn is the module name
   *  mn is the safe method name
   *  sig is the method signature
   */
  def leonFunDefToJVMInfo(fd: FunDef): Option[(String, String, String)] = {
    funDefInfo.get(fd).orElse {
      val monitorType = if (params.requireMonitor) "L"+MonitorClass+";" else ""

      val sig = "(" + monitorType + fd.params.map(a => typeToJVM(a.getType)).mkString("") + ")" + typeToJVM(fd.returnType)

      defToModuleOrClass.get(fd).flatMap(m => classes.get(m)) match {
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
          val conss = klass.getConstructors.sortBy(_.getParameterTypes.length)
          assert(conss.nonEmpty)
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
    val conss = tc.getConstructors.sortBy(_.getParameterTypes.length)
    assert(conss.nonEmpty)
    conss.last
  }

  // Currently, this method is only used to prepare arguments to reflective calls.
  // This means it is safe to return AnyRef (as opposed to primitive types), because
  // reflection needs this anyway.
  def exprToJVM(e: Expr)(implicit monitor : LeonCodeGenRuntimeMonitor): AnyRef = e match {
    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case InfiniteIntegerLiteral(v) =>
      new leon.codegen.runtime.BigInt(v.toString)

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case GenericValue(tp, id) =>
      e

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(exprToJVM).toArray).asInstanceOf[AnyRef]

    case CaseClass(cct, args) =>
      caseClassConstructor(cct.classDef) match {
        case Some(cons) =>
          val realArgs = if (params.requireMonitor) monitor +: args.map(exprToJVM) else  args.map(exprToJVM)
          cons.newInstance(realArgs.toArray : _*).asInstanceOf[AnyRef]
        case None =>
          ctx.reporter.fatalError("Case class constructor not found?!?")
      }

    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    //case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType) =>
    //  exprs.map(e => exprToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray

    case s @ FiniteSet(els) =>
      val s = new leon.codegen.runtime.Set()
      for (e <- els) {
        s.add(exprToJVM(e))
      }
      s

    case m @ FiniteMap(els) =>
      val m = new leon.codegen.runtime.Map()
      for ((k,v) <- els) {
        m.add(exprToJVM(k), exprToJVM(v))
      }
      m

    case f @ purescala.Extractors.FiniteLambda(dflt, els) =>
      val l = new leon.codegen.runtime.FiniteLambda(exprToJVM(dflt))

      for ((k,v) <- els) {
        val ks = unwrapTuple(k, f.getType.asInstanceOf[FunctionType].from.size)
        // Force tuple even with 1/0 elems.
        val kJvm = tupleConstructor.newInstance(ks.map(exprToJVM).toArray).asInstanceOf[leon.codegen.runtime.Tuple]
        val vJvm = exprToJVM(v)
        l.add(kJvm,vJvm)
      }
      l

    // Just slightly overkill...
    case _ =>
      compileExpression(e, Seq()).evalToJVM(Seq(),monitor)
  }

  // Note that this may produce untyped expressions! (typically: sets, maps)
  def jvmToExpr(e: AnyRef, tpe: TypeTree): Expr = (e, tpe) match {
    case (i: Integer, Int32Type) =>
      IntLiteral(i.toInt)

    case (c: runtime.BigInt, IntegerType) =>
      InfiniteIntegerLiteral(BigInt(c.underlying))

    case (b: java.lang.Boolean, BooleanType) =>
      BooleanLiteral(b.booleanValue)

    case (c: java.lang.Character, CharType) =>
      CharLiteral(c.toChar)

    case (cc: runtime.CaseClass, ct: ClassType) =>
      val fields = cc.productElements()

      // identify case class type of ct
      val cct = ct match {
        case cc: CaseClassType =>
          cc

        case _ =>
          jvmClassToLeonClass(cc.getClass.getName) match {
            case Some(cc: CaseClassDef) =>
              CaseClassType(cc, ct.tps)
            case _ =>
              throw CompilationException("Unable to identify class "+cc.getClass.getName+" to descendent of "+ct)
        }
      }

      CaseClass(cct, (fields zip cct.fieldsTypes).map { case (e, tpe) => jvmToExpr(e, tpe) })

    case (tpl: runtime.Tuple, tpe) =>
      val stpe = unwrapTupleType(tpe, tpl.getArity)
      val elems = stpe.zipWithIndex.map { case (tpe, i) => 
        jvmToExpr(tpl.get(i), tpe)
      }
      tupleWrap(elems)

    case (gv @ GenericValue(gtp, id), tp: TypeParameter) =>
      if (gtp == tp) gv
      else GenericValue(tp, id).copiedFrom(gv)

    case (set : runtime.Set, SetType(b)) =>
      finiteSet(set.getElements.asScala.map(jvmToExpr(_, b)).toSet, b)

    case (map : runtime.Map, MapType(from, to)) =>
      val pairs = map.getElements.asScala.map { entry =>
        val k = jvmToExpr(entry.getKey, from)
        val v = jvmToExpr(entry.getValue, to)
        (k, v)
      }
      finiteMap(pairs.toSeq, from, to)

    case _ =>
      throw CompilationException("Unsupported return value : " + e.getClass +" while expecting "+tpe)
  }

  var compiledN = 0

  def compileExpression(e: Expr, args: Seq[Identifier]): CompiledExpression = {
    if(e.getType == Untyped) {
      throw new IllegalArgumentException(s"Cannot compile untyped expression [$e].")
    }

    compiledN += 1

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

    mkExpr(e, ch)(Locals(newMapping, Map.empty, Map.empty, true))

    e.getType match {
      case Int32Type | BooleanType | UnitType =>
        ch << IRETURN

      case IntegerType | _: TupleType  | _: SetType | _: MapType | _: AbstractClassType | _: CaseClassType | _: ArrayType | _: FunctionType | _: TypeParameter =>
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
    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])
    
    /*if (false) {
      // currently we do not handle object fields 
      // this treats all fields as functions
      for (fun <- module.definedFunctions) {
        compileFunDef(fun, module)
      }
    } else {*/
    
    val (fields, functions) = module.definedFunctions partition { _.canBeField }
    val (strictFields, lazyFields) = fields partition { _.canBeStrictField }
    
    // Compile methods
    for (function <- functions) {
      compileFunDef(function,module)
    }
    
    // Compile lazy fields
    for (lzy <- lazyFields) {
      compileLazyField(lzy, module)
    }
    
    // Compile strict fields
    for (field <- strictFields) {
      compileStrictField(field, module)
    }
 
    // Constructor
    cf.addDefaultConstructor
    
    val cName = defToJVMName(module)
    
    // Add class initializer method
    locally{ 
      val mh = cf.addMethod("V", "<clinit>")
      mh.setFlags((
        METHOD_ACC_STATIC | 
        METHOD_ACC_PUBLIC
      ).asInstanceOf[U2])
      
      val ch = mh.codeHandler
      /*
       * FIXME :
       * Dirty hack to make this compatible with monitoring of method invocations.
       * Because we don't have access to the monitor object here, we initialize a new one 
       * that will get lost when this method returns, so we can't hope to count 
       * method invocations here :( 
       */
      ch << New(MonitorClass) << DUP
      ch << Ldc(Int.MaxValue) // Allow "infinite" method calls
      ch << InvokeSpecial(MonitorClass, cafebabe.Defaults.constructorName, "(I)V")
      ch << AStore(ch.getFreshVar) // position 0
      for (lzy <- lazyFields) { initLazyField(ch, cName, lzy, true)}  
      for (field <- strictFields) { initStrictField(ch, cName , field, true)}
      ch  << RETURN
      ch.freeze
    }
      
    

  
  }

  /** Traverses the program to find all definitions, and stores those in global variables */
  def init() {
    // First define all classes/ methods/ functions
    for (u <- program.units; m <- u.modules) {
      val (parents, children) = m.algebraicDataTypes.toSeq.unzip
      for ( cls <- parents ++ children.flatten ++ m.singleCaseClasses) {
        defineClass(cls)
        for (meth <- cls.methods) {
          defToModuleOrClass += meth -> cls
        }
      }
     
      defineClass(m)
      for(funDef <- m.definedFunctions) {
        defToModuleOrClass += funDef -> m
      }
      
    }
  }

  /** Compiles the program. Uses information provided by $init */
  def compile() {
    // Compile everything
    for (u <- program.units) {
      
      for ((parent, children) <- u.algebraicDataTypes) {
        compileAbstractClassDef(parent)

        for (c <- children) {
          compileCaseClassDef(c)
        }
      }

      for(single <- u.singleCaseClasses) {
        compileCaseClassDef(single)
      }

      for (m <- u.modules) compileModule(m)
      
    }

    classes.values.foreach(loader.register)
  }

  def writeClassFiles(prefix: String) {
    for ((d, cl) <- classes) {
      cl.writeToFile(prefix+cl.className + ".class")
    }
  }

  init()
  compile()
}

object CompilationUnit {
  private var _nextExprId = 0
  private[codegen] def nextExprId = synchronized {
    _nextExprId += 1
    _nextExprId
  }

  private var _nextLambdaId = 0
  private[codegen] def nextLambdaId = synchronized {
    _nextLambdaId += 1
    _nextLambdaId
  }
}

