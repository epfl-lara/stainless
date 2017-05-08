/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package codegen

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Defaults.constructorName
import cafebabe.Flags._

import inox.utils._

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

case class CompilationException(msg: String) extends Exception(msg)

object optInstrumentFields extends inox.FlagOptionDef("instrument", false)
object optSmallArrays extends inox.FlagOptionDef("smallarrays", false)

trait CodeGeneration { self: CompilationUnit =>
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._

  val maxSteps: Int

  lazy val ignoreContracts = options.findOptionOrDefault(inox.evaluators.optIgnoreContracts)
  lazy val doInstrument = options.findOptionOrDefault(optInstrumentFields)
  lazy val smallArrays = options.findOptionOrDefault(optSmallArrays)
  lazy val recordInvocations = maxSteps >= 0

  /** A class providing information about the status of parameters in the function that is being currently compiled.
   *  vars is a mapping from local variables/ parameters to the offset of the respective JVM local register
   *  isStatic signifies if the current method is static (a function, in Stainless terms)
   */
  class Locals private[codegen] (
    vars    : Map[Identifier, Int],
    args    : Map[Identifier, Int],
    fields  : Map[Identifier, (String,String,String)],
    val params  : Seq[ValDef],
    val tparams : Seq[TypeParameter]
  ) {
    /** Fetches the offset of a local variable/ parameter from its identifier */
    def varToLocal(v: Identifier): Option[Int] = vars.get(v)

    def varToArg(v: Identifier): Option[Int] = args.get(v)

    def varToField(v: Identifier): Option[(String,String,String)] = fields.get(v)

    /** Adds some extra variables to the mapping */
    def withVars(newVars: Map[Identifier, Int]) = new Locals(vars ++ newVars, args, fields, params, tparams)

    /** Adds an extra variable to the mapping */
    def withVar(nv: (Identifier, Int)) = new Locals(vars + nv, args, fields, params, tparams)

    def withArgs(newArgs: Map[Identifier, Int]) = new Locals(vars, args ++ newArgs, fields, params, tparams)

    def withFields(newFields: Map[Identifier,(String,String,String)]) = new Locals(vars, args, fields ++ newFields, params, tparams)

    def withParameters(newParams: Seq[ValDef]) = new Locals(vars, args, fields, params ++ newParams, tparams)
    def withTypeParameters(newTps: Seq[TypeParameter]) = new Locals(vars, args, fields, params, tparams ++ newTps)

    def substitute(subst: Map[Identifier, Identifier]) = new Locals(
      vars.map(p => subst.getOrElse(p._1, p._1) -> p._2),
      args.map(p => subst.getOrElse(p._1, p._1) -> p._2),
      fields.map(p => subst.getOrElse(p._1, p._1) -> p._2),
      params, tparams)

    override def toString = "Locals("+vars + ", " + args + ", " + fields + ", " + params + ", " + tparams + ")"
  }

  object NoLocals extends Locals(Map.empty, Map.empty, Map.empty, Seq.empty, Seq.empty)

  lazy val monitorID = FreshIdentifier("__$monitor")
  lazy val tpsID     = FreshIdentifier("__$tps")

  private[codegen] val ObjectClass               = "java/lang/Object"
  private[codegen] val BoxedIntClass             = "java/lang/Integer"
  private[codegen] val BoxedBoolClass            = "java/lang/Boolean"
  private[codegen] val BoxedCharClass            = "java/lang/Character"
  private[codegen] val BoxedArrayClass           = "leon/codegen/runtime/BoxedArray"

  private[codegen] val JavaListClass             = "java/util/List"
  private[codegen] val JavaIteratorClass         = "java/util/Iterator"
  private[codegen] val JavaStringClass           = "java/lang/String"

  private[codegen] val TupleClass                = "stainless/codegen/runtime/Tuple"
  private[codegen] val SetClass                  = "stainless/codegen/runtime/Set"
  private[codegen] val BagClass                  = "stainless/codegen/runtime/Bag"
  private[codegen] val MapClass                  = "stainless/codegen/runtime/Map"
  private[codegen] val ArrayClass                = "stainless/codegen/runtime/BigArray"
  private[codegen] val BigIntClass               = "stainless/codegen/runtime/BigInt"
  private[codegen] val BitVectorClass            = "stainless/codegen/runtime/BitVector"
  private[codegen] val RationalClass             = "stainless/codegen/runtime/Rational"
  private[codegen] val ADTClass                  = "stainless/codegen/runtime/ADT"
  private[codegen] val LambdaClass               = "stainless/codegen/runtime/Lambda"
  private[codegen] val ErrorClass                = "stainless/codegen/runtime/CodeGenRuntimeException"
  private[codegen] val ChooseEntryPointClass     = "stainless/codegen/runtime/ChooseEntryPoint"
  private[codegen] val GenericValuesClass        = "stainless/codegen/runtime/GenericValues"
  private[codegen] val MonitorClass              = "stainless/codegen/runtime/Monitor"
  private[codegen] val StringOpsClass            = "stainless/codegen/runtime/StringOps"

  private[codegen] val HashingClass              = "scala/util/hashing/MurmurHash3"

  def idToSafeJVMName(id: Identifier) = {
    scala.reflect.NameTransformer.encode(id.uniqueName).replaceAll("\\.", "\\$")
  }

  def defToJVMName(d: Definition): String = "Stainless$CodeGen$Def$" + idToSafeJVMName(d.id)

  private[this] val adtClassFiles : MutableMap[ADTDefinition, ClassFile] = MutableMap.empty
  private[this] val classToADT    : MutableMap[String, ADTDefinition]    = MutableMap.empty

  def getClass(adt: ADTDefinition): ClassFile = adtClassFiles.get(adt) match {
    case Some(cf) => cf
    case None =>
      val cName = defToJVMName(adt)
      val pName = adt match {
        case cons: ADTConstructor => cons.sort.map(id => defToJVMName(getADT(id)))
        case _ => None
      }

      val cf = new ClassFile(cName, pName)
      classToADT += cf.className -> adt
      adtClassFiles += adt -> cf
      cf
  }

  private[this] lazy val static = new ClassFile("<static>", None)

  protected def compile(): Seq[ClassFile] = {
    for (adt <- adts.values) adt match {
      case sort: ADTSort => compileADTSort(sort)
      case cons: ADTConstructor => compileADTConstructor(cons)
    }

    for (fd <- functions.values) {
      compileFunDef(fd, static)
    }

    adtClassFiles.values.toSeq :+ static
  }

  protected def jvmClassNameToADT(className: String): Option[ADTDefinition] = classToADT.get(className)

  private[this] val adtInfos: MutableMap[ADTDefinition, (String, String)] = MutableMap.empty

  protected def getADTInfo(adt: ADTDefinition): (String, String) = adtInfos.getOrElseUpdate(adt, {
    val cf = getClass(adt)
    val tpeParam = if (adt.tparams.isEmpty) "" else "[I"
    val sig = "(L"+MonitorClass+";" + tpeParam + (adt match {
      case cons: ADTConstructor => cons.fields.map(f => typeToJVM(f.tpe)).mkString("")
      case _ => ""
    }) + ")V"
    (cf.className, sig)
  })

  private[this] val funDefInfos: MutableMap[FunDef, (String, String, String)] = MutableMap.empty

  protected def getFunDefInfo(fd: FunDef): (String, String, String) = funDefInfos.getOrElseUpdate(fd, {
    val sig = "(L"+MonitorClass+";" +
      (if (fd.tparams.nonEmpty) "[I" else "") +
      fd.params.map(a => typeToJVM(a.tpe)).mkString("") + ")" + typeToJVM(fd.returnType)

    (static.className, idToSafeJVMName(fd.id), sig)
  })

  protected object ValueType {
    def unapply(tp: Type): Boolean = tp match {
      case Int32Type | BooleanType | CharType | UnitType => true
      case _ => false
    }
  }

  /** Return the respective JVM type from a Stainless type */
  def typeToJVM(tpe: Type) : String = tpe match {
    case Int32Type => "I"

    case BooleanType => "Z"

    case CharType => "C"

    case UnitType => "Z"

    case adt: ADTType =>
      val (n, _) = getADTInfo(adt.getADT.definition)
      s"L$n;"

    case _ : TupleType =>
      "L" + TupleClass + ";"

    case _ : SetType =>
      "L" + SetClass + ";"

    case _ : BagType =>
      "L" + BagClass + ";"

    case _ : MapType =>
      "L" + MapClass + ";"

    case IntegerType =>
      "L" + BigIntClass + ";"

    case RealType =>
      "L" + RationalClass + ";"

    case _ : FunctionType =>
      "L" + LambdaClass + ";"

    case ArrayType(base) =>
      if (smallArrays) "[" + typeToJVM(base)
      else "L" + ArrayClass + ";"

    case _: TypeParameter =>
      "L" + ObjectClass + ";"
    
    case StringType =>
      "L" + JavaStringClass + ";"

    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  /** Return the respective boxed JVM type from a Stainless type */
  def typeToJVMBoxed(tpe: Type) : String = tpe match {
    case Int32Type              => s"L$BoxedIntClass;"
    case BooleanType | UnitType => s"L$BoxedBoolClass;"
    case CharType               => s"L$BoxedCharClass;"
    case other                  => typeToJVM(other)
  }

  /**
   * Compiles a function/method definition.
   * @param funDef The function definition to be compiled
   * @param owner The module/class that contains `funDef`
   */
  def compileFunDef(funDef: FunDef, cf: ClassFile): Unit = {
    val (_,mn,_) = getFunDefInfo(funDef)

    val tpeParam = if (funDef.tparams.isEmpty) Seq() else Seq("[I")
    val realParams = ("L" + MonitorClass + ";") +: (tpeParam ++ funDef.params.map(a => typeToJVM(a.getType)))

    val m = cf.addMethod(
      typeToJVM(funDef.returnType),
      mn,
      realParams : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL  |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val paramIds = Seq(monitorID) ++ 
      (if (funDef.tparams.nonEmpty) Seq(tpsID) else Seq.empty) ++
      funDef.params.map(_.id)

    val newMapping = paramIds.zipWithIndex.toMap

    val body = if (!ignoreContracts) {
      funDef.fullBody
    } else {
      funDef.body.getOrElse(
        // TODO: externs!!
        /*
        if (funDef.annotations contains "extern") {
          Error(funDef.id.getType, "Body of " + funDef.id.name + " not implemented at compile-time and still executed.")
        } else {*/
          throw CompilationException("Can't compile a FunDef without body: "+funDef.id.name)
        )
    }

    val locals = NoLocals.withVars(newMapping)
      .withParameters(funDef.params)
      .withTypeParameters(funDef.tparams.map(_.tp))

    if (recordInvocations) {
      load(monitorID, ch)(locals)
      ch << InvokeVirtual(MonitorClass, "onInvocation", "()V")
    }

    mkExpr(body, ch)(locals)

    funDef.returnType match {
      case ValueType() =>
        ch << IRETURN

      case _ =>
        ch << ARETURN
    }

    ch.freeze
  }

  private[this] val lambdaClasses = new Bijection[Lambda, String]

  protected def jvmClassNameToLambda(className: String): Option[Lambda] = lambdaClasses.getA(className)

  private val typeParams: ListBuffer[TypeParameter] = new ListBuffer[TypeParameter]

  protected def compileLambda(l: Lambda, params: Seq[ValDef], pre: Boolean = false):
                             (String, Seq[(Identifier, String)], Seq[TypeParameter], String) = {
    assert(normalizeStructure(l)._1 == l)

    var tpParams = typeParams.toList
    var tpSubst: Map[TypeParameter, TypeParameter] = Map.empty
    def subst(tp: TypeParameter): TypeParameter = tpSubst.getOrElse(tp, {
      val fresh = tpParams match {
        case x :: xs =>
          tpParams = xs
          x
        case Nil =>
          val tp = TypeParameter.fresh("Tp")
          typeParams += tp
          tp
      }
      tpSubst += tp -> fresh
      fresh
    })

    object normalizer extends {
      val s: program.trees.type = program.trees
      val t: program.trees.type = program.trees
    } with ast.TreeTransformer {
      override def transform(tpe: Type): Type = tpe match {
        case tp: TypeParameter => subst(tp)
        case _ => super.transform(tpe)
      }
    }

    val lambda = normalizer.transform(l).asInstanceOf[Lambda]
    val (tparams, tps) = tpSubst.toSeq.sortBy(_._2.id.uniqueName).unzip

    val closedVars = variablesOf(lambda).toSeq.sortBy(_.id.uniqueName)

    val closuresWithoutMonitor = closedVars.map(v => v -> typeToJVM(v.tpe))
    val closures = (monitorID -> s"L$MonitorClass;") +:
      ((if (tps.nonEmpty) Seq(tpsID -> "[I") else Seq.empty) ++
      closuresWithoutMonitor.map(p => p._1.id -> p._2))

    val afName = lambdaClasses.getB(lambda) match {
      case Some(afName) => afName
      case None =>
        val afId = FreshIdentifier("Stainless$CodeGen$Lambda$")
        val afName = afId.uniqueName
        lambdaClasses += lambda -> afName

        val cf = new ClassFile(afName, Some(LambdaClass))

        cf.setFlags((
          CLASS_ACC_SUPER |
          CLASS_ACC_PUBLIC |
          CLASS_ACC_FINAL
        ).asInstanceOf[U2])

        if (closures.isEmpty) {
          cf.addDefaultConstructor
        } else {
          for ((id, jvmt) <- closures) {
            val fh = cf.addField(jvmt, id.uniqueName)
            fh.setFlags((
              FIELD_ACC_PUBLIC |
              FIELD_ACC_FINAL
            ).asInstanceOf[U2])
          }

          val cch = cf.addConstructor(closures.map(_._2).toList).codeHandler

          cch << ALoad(0)
          cch << InvokeSpecial(LambdaClass, constructorName, "()V")

          var c = 1
          for ((id, jvmt) <- closures) {
            cch << ALoad(0)
            cch << (jvmt match {
              case "I" | "Z" => ILoad(c)
              case _ => ALoad(c)
            })
            cch << PutField(afName, id.uniqueName, jvmt)
            c += 1
          }

          cch << RETURN
          cch.freeze
        }

        val argMapping = lambda.args.zipWithIndex.map { case (v, i) => v.id -> i }.toMap
        val closureMapping = closures.map { case (id, jvmt) => id -> (afName, id.uniqueName, jvmt) }.toMap
        val newLocals = NoLocals.withArgs(argMapping).withFields(closureMapping)
          .withParameters(params ++ l.args).withTypeParameters(tps)

        locally {
          val pm = cf.addMethod(s"L$LambdaClass;", "pre", "")

          pm.setFlags((
            METHOD_ACC_PUBLIC |
            METHOD_ACC_FINAL
          ).asInstanceOf[U2])

          val pch = pm.codeHandler

          val preLocals = NoLocals.withFields(closureMapping)
            .withParameters(params)
            .withTypeParameters(tps)

          val preLambda = if (pre) {
            lambda.copy(body = BooleanLiteral(true))
          } else {
            lambda.copy(body = weakestPrecondition(lambda.body))
          }

          mkLambda(preLambda, pch, pre = true)(preLocals)

          pch << ARETURN

          pch.freeze
        }

        locally {
          val apm = cf.addMethod(s"L$ObjectClass;", "apply", s"[L$ObjectClass;")

          apm.setFlags((
            METHOD_ACC_PUBLIC |
            METHOD_ACC_FINAL
          ).asInstanceOf[U2])

          val apch = apm.codeHandler

          mkBoxedExpr(lambda.body, apch)(newLocals)

          apch << ARETURN

          apch.freeze
        }

        locally {
          val emh = cf.addMethod("Z", "equals", s"L$ObjectClass;")
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
          ech << ALoad(1) << InstanceOf(afName) << IfEq(notEq)

          // ...finally, we compare fields one by one, shortcircuiting on disequalities.
          if (closures.nonEmpty) {
            ech << ALoad(1) << CheckCast(afName) << AStore(castSlot)

            for ((v, jvmt) <- closuresWithoutMonitor) {
              ech << ALoad(0) << GetField(afName, v.id.uniqueName, jvmt)
              mkArrayBox(v.tpe, ech)

              ech << ALoad(castSlot) << GetField(afName, v.id.uniqueName, jvmt)

              v.tpe match {
                case ValueType() =>
                  ech << If_ICmpNe(notEq)

                case ot =>
                  ech << InvokeVirtual(ObjectClass, "equals", s"(L$ObjectClass;)Z") << IfEq(notEq)
              }
            }
          }

          ech << Ldc(1) << IRETURN << Label(notEq) << Ldc(0) << IRETURN
          ech.freeze
        }

        locally {
          val hashFieldName = "$leon$hashCode"
          cf.addField("I", hashFieldName).setFlags(FIELD_ACC_PRIVATE)
          val hmh = cf.addMethod("I", "hashCode", "")
          hmh.setFlags((
            METHOD_ACC_PUBLIC |
            METHOD_ACC_FINAL
          ).asInstanceOf[U2])

          val hch = hmh.codeHandler

          val wasNotCached = hch.getFreshLabel("wasNotCached")

          hch << ALoad(0) << GetField(afName, hashFieldName, "I") << DUP
          hch << IfEq(wasNotCached)
          hch << IRETURN
          hch << Label(wasNotCached) << POP

          hch << Ldc(closuresWithoutMonitor.size) << NewArray(s"$ObjectClass")
          for (((v, jvmt),i) <- closuresWithoutMonitor.zipWithIndex) {
            hch << DUP << Ldc(i)
            hch << ALoad(0) << GetField(afName, v.id.uniqueName, jvmt)
            mkBox(v.tpe, hch)
            hch << AASTORE
          }

          hch << Ldc(afName.hashCode)
          hch << InvokeStatic(HashingClass, "arrayHash", s"([L$ObjectClass;I)I") << DUP
          hch << ALoad(0) << SWAP << PutField(afName, hashFieldName, "I")
          hch << IRETURN

          hch.freeze
        }

        loader.register(cf)

        afName
    }

    (afName, closures, tparams, "(" + closures.map(_._2).mkString("") + ")V")
  }

  // also makes tuples with 0/1 args
  private def mkTuple(es: Seq[Expr], ch: CodeHandler)(implicit locals: Locals) : Unit = {
    ch << New(TupleClass) << DUP
    ch << Ldc(es.size)
    ch << NewArray(s"$ObjectClass")
    for ((e,i) <- es.zipWithIndex) {
      ch << DUP
      ch << Ldc(i)
      mkBoxedExpr(e, ch)
      ch << AASTORE
    }
    ch << InvokeSpecial(TupleClass, constructorName, s"([L$ObjectClass;)V")
  }

  private def loadTypes(tps: Seq[Type], ch: CodeHandler)(implicit locals: Locals): Unit = {
    if (tps.nonEmpty) {
      ch << Ldc(tps.size)
      ch << NewArray.primitive("T_INT")
      for ((tpe,idx) <- tps.zipWithIndex) {
        ch << DUP << Ldc(idx) << Ldc(registerType(tpe)) << IASTORE
      }

      if (locals.tparams.nonEmpty) {
        load(monitorID, ch)
        ch << SWAP

        ch << Ldc(locals.tparams.size)
        ch << NewArray.primitive("T_INT")
        for ((tpe,idx) <- locals.tparams.zipWithIndex) {
          ch << DUP << Ldc(idx) << Ldc(registerType(tpe)) << IASTORE
        }

        ch << SWAP
        load(tpsID, ch)
        ch << InvokeVirtual(MonitorClass, "typeParams", s"([I[I[I)[I")
      }
    }
  }

  private[codegen] def mkExpr(e: Expr, ch: CodeHandler, canDelegateToMkBranch: Boolean = true)
                             (implicit locals: Locals): Unit = e match {
    case v: Variable =>
      load(v, ch)

    case Assert(cond, oerr, body) =>
      mkExpr(IfExpr(Not(cond), Error(body.getType, oerr.getOrElse("Assertion failed @"+e.getPos)), body), ch)

    case en @ Ensuring(_, _) =>
      mkExpr(en.toAssert, ch)

    case Require(pre, body) =>
      mkExpr(IfExpr(pre, body, Error(body.getType, "Precondition failed")), ch)

    case Let(vd, d, v) if vd.toVariable == v => // Optimization for local variables.
      mkExpr(d, ch)

    case Let(vd, d, Let(vd2, v, v2)) if vd.toVariable == v && vd2.toVariable == v2 => // Optimization for local variables.
      mkExpr(d, ch)

    case Let(vd,d,b) =>
      mkExpr(d, ch)
      val slot = ch.getFreshVar
      ch << (vd.tpe match {
        case ValueType() =>
          if (slot > 127) {
            println("Error while converting one more slot which is too much " + e)
          }
          IStore(slot)
        case _ => AStore(slot)
      })
      mkExpr(b, ch)(locals.withVar(vd.id -> slot))

    case Int32Literal(v) =>
      ch << Ldc(v)

    case CharLiteral(v) =>
      ch << Ldc(v)

    case BooleanLiteral(v) =>
      ch << Ldc(if(v) 1 else 0)

    case UnitLiteral() =>
      ch << Ldc(1)
    
    case StringLiteral(v) =>
      ch << Ldc(v)

    case IntegerLiteral(v) =>
      ch << New(BigIntClass) << DUP
      ch << Ldc(v.toString)
      ch << InvokeSpecial(BigIntClass, constructorName, "(Ljava/lang/String;)V")

    case FractionLiteral(n, d) =>
      ch << New(RationalClass) << DUP
      ch << Ldc(n.toString)
      ch << Ldc(d.toString)
      ch << InvokeSpecial(RationalClass, constructorName, "(Ljava/lang/String;Ljava/lang/String;)V")

    case ADT(adt, as) =>
      val tcons = adt.getADT.toConstructor
      val cons = tcons.definition
      val (adtName, adtApplySig) = getADTInfo(cons)
      ch << New(adtName) << DUP
      load(monitorID, ch)
      loadTypes(adt.tps, ch)

      for ((a, vd) <- as zip cons.fields) {
        vd.tpe match {
          case _: TypeParameter =>
            mkBoxedExpr(a, ch)
          case _ =>
            mkExpr(a, ch)
        }
      }
      ch << InvokeSpecial(adtName, constructorName, adtApplySig)

      // check invariant (if it exists)
      if (!ignoreContracts && cons.hasInvariant) {
        ch << DUP

        val tfd = tcons.invariant.get
        val (cn, mn, ms) = getFunDefInfo(tfd.fd)

        load(monitorID, ch)
        ch << SWAP // stack: (monitor, adt)

        if (tfd.tps.nonEmpty) {
          loadTypes(tfd.tps, ch)
          ch << SWAP // stack: (monitor, tps, adt)
        }

        ch << InvokeStatic(cn, mn, ms)

        val ok = ch.getFreshLabel("invariant_ok")
        ch << IfNe(ok)
        mkExpr(Error(BooleanType, "ADT invariant failed @" + e.getPos), ch)
        ch << Label(ok)
      }

    case IsInstanceOf(e, adt: ADTType) =>
      val (ccName, _) = getADTInfo(adt.getADT.definition)
      mkExpr(e, ch)
      ch << InstanceOf(ccName)

    case AsInstanceOf(e, adt: ADTType) =>
      val (ccName, _) = getADTInfo(adt.getADT.definition)
      mkExpr(e, ch)
      ch << CheckCast(ccName)

    case ADTSelector(IsTyped(e, adt: ADTType), sid) =>
      mkExpr(e, ch)
      val (ccName, _) = getADTInfo(adt.getADT.definition)
      ch << CheckCast(ccName)
      instrumentedGetField(ch, adt, sid)

    // Tuples (note that instanceOf checks are in mkBranch)
    case Tuple(es) => mkTuple(es, ch)

    case TupleSelect(t, i) =>
      val TupleType(bs) = t.getType
      mkExpr(t,ch)
      ch << Ldc(i - 1)
      ch << InvokeVirtual(TupleClass, "get", s"(I)L$ObjectClass;")
      mkUnbox(bs(i - 1), ch)

    // Sets
    case FiniteSet(es, _) =>
      ch << DefaultNew(SetClass)
      for(e <- es) {
        ch << DUP
        mkBoxedExpr(e, ch)
        ch << InvokeVirtual(SetClass, "insert", s"(L$ObjectClass;)V")
      }

    case SetAdd(s, e) =>
      mkExpr(s, ch)
      mkBoxedExpr(e, ch)
      ch << InvokeVirtual(SetClass, "add", s"(L$ObjectClass;)L$SetClass;")

    case ElementOfSet(e, s) =>
      mkExpr(s, ch)
      mkBoxedExpr(e, ch)
      ch << InvokeVirtual(SetClass, "contains", s"(L$ObjectClass;)Z")

    case SubsetOf(s1, s2) =>
      mkExpr(s1, ch)
      mkExpr(s2, ch)
      ch << InvokeVirtual(SetClass, "subsetOf", s"(L$SetClass;)Z")

    case SetIntersection(s1, s2) =>
      mkExpr(s1, ch)
      mkExpr(s2, ch)
      ch << InvokeVirtual(SetClass, "intersect", s"(L$SetClass;)L$SetClass;")

    case SetUnion(s1, s2) =>
      mkExpr(s1, ch)
      mkExpr(s2, ch)
      ch << InvokeVirtual(SetClass, "union", s"(L$SetClass;)L$SetClass;")

    case SetDifference(s1, s2) =>
      mkExpr(s1, ch)
      mkExpr(s2, ch)
      ch << InvokeVirtual(SetClass, "difference", s"(L$SetClass;)L$SetClass;")

    // Bags
    case FiniteBag(els, _) =>
      ch << DefaultNew(BagClass)
      for((k,v) <- els) {
        ch << DUP
        mkBoxedExpr(k, ch)
        mkExpr(v, ch)
        ch << InvokeVirtual(BagClass, "insert", s"(L$ObjectClass;L$BigIntClass;)V")
      }

    case BagAdd(b, e) =>
      mkExpr(b, ch)
      mkBoxedExpr(e, ch)
      ch << InvokeVirtual(BagClass, "add", s"(L$ObjectClass;)L$BagClass;")

    case MultiplicityInBag(e, b) =>
      mkExpr(b, ch)
      mkBoxedExpr(e, ch)
      ch << InvokeVirtual(BagClass, "get", s"(L$ObjectClass;)L$BigIntClass;")

    case BagIntersection(b1, b2) =>
      mkExpr(b1, ch)
      mkExpr(b2, ch)
      ch << InvokeVirtual(BagClass, "intersect", s"(L$BagClass;)L$BagClass;")

    case BagUnion(b1, b2) =>
      mkExpr(b1, ch)
      mkExpr(b2, ch)
      ch << InvokeVirtual(BagClass, "union", s"(L$BagClass;)L$BagClass;")

    case BagDifference(b1, b2) =>
      mkExpr(b1, ch)
      mkExpr(b2, ch)
      ch << InvokeVirtual(BagClass, "difference", s"(L$BagClass;)L$BagClass;")

    // Maps
    case FiniteMap(ss, dflt, _, _) =>
      ch << New(MapClass) << DUP
      mkBoxedExpr(dflt, ch)
      ch << InvokeSpecial(MapClass, constructorName, s"(L$ObjectClass;)V")
      for ((f,t) <- ss) {
        ch << DUP
        mkBoxedExpr(f, ch)
        mkBoxedExpr(t, ch)
        ch << InvokeVirtual(MapClass, "insert", s"(L$ObjectClass;L$ObjectClass;)V")
      }

    case MapApply(m, k) =>
      val MapType(_, tt) = m.getType
      mkExpr(m, ch)
      mkBoxedExpr(k, ch)
      ch << InvokeVirtual(MapClass, "get", s"(L$ObjectClass;)L$ObjectClass;")
      mkUnbox(tt, ch)

    case MapUpdated(map, key, value) =>
      mkExpr(map, ch)
      mkBoxedExpr(key, ch)
      mkBoxedExpr(value, ch)
      ch << InvokeVirtual(MapClass, "updated", s"(L$ObjectClass;L$ObjectClass;)L$MapClass;")

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

    // Static lazy fields/ functions
    case fi @ FunctionInvocation(id, tps, as) =>
      val tfd = getFunction(id, tps)
      val (cn, mn, ms) = getFunDefInfo(tfd.fd)

      load(monitorID, ch)
      loadTypes(tfd.tps, ch)

      for ((a, vd) <- as zip tfd.fd.params) {
        vd.getType match {
          case _: TypeParameter =>
            mkBoxedExpr(a, ch)
          case _ =>
            mkExpr(a, ch)
        }
      }

      ch << InvokeStatic(cn, mn, ms)

      (tfd.fd.returnType, tfd.returnType) match {
        case (_: TypeParameter, tpe)  =>
          mkUnbox(tpe, ch)
        case _ =>
      }

    case app @ Application(caller, args) =>
      mkExpr(caller, ch)
      ch << Ldc(args.size) << NewArray(s"$ObjectClass")
      for ((arg,i) <- args.zipWithIndex) {
        ch << DUP << Ldc(i)
        mkBoxedExpr(arg, ch)
        ch << AASTORE
      }

      ch << InvokeVirtual(LambdaClass, "apply", s"([L$ObjectClass;)L$ObjectClass;")
      mkUnbox(app.getType, ch)

    case Pre(f) =>
      mkExpr(f, ch)
      ch << InvokeVirtual(LambdaClass, "pre", s"()L$LambdaClass;")

    case lambda: Lambda =>
      mkLambda(lambda, ch, pre = false)

    // String processing =>
    case StringConcat(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      ch << InvokeStatic(StringOpsClass, "concat", s"(L$JavaStringClass;L$JavaStringClass;)L$JavaStringClass;")

    case StringLength(a) =>
      mkExpr(a, ch)
      ch << InvokeStatic(StringOpsClass, "length", s"(L$JavaStringClass;)L$BigIntClass;")
      
    case SubString(a, start, end) =>
      mkExpr(a, ch)
      mkExpr(start, ch)
      mkExpr(end, ch)
      ch << InvokeStatic(StringOpsClass, "substring", s"(L$JavaStringClass;L$BigIntClass;L$BigIntClass;)L$JavaStringClass;")
      
    // Arithmetic
    case Plus(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "add", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          ch << IADD
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "add", s"(L$BitVectorClass;)L$BitVectorClass;")
        case RealType =>
          ch << InvokeVirtual(RationalClass, "add", s"(L$RationalClass;)L$RationalClass;")
      }

    case Minus(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "sub", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          ch << ISUB
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "sub", s"(L$BitVectorClass;)L$BitVectorClass;")
        case RealType =>
          ch << InvokeVirtual(RationalClass, "sub", s"(L$RationalClass;)L$RationalClass;")
      }

    case Times(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "mult", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          ch << IMUL
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "mult", s"(L$BitVectorClass;)L$BitVectorClass;")
        case RealType =>
          ch << InvokeVirtual(RationalClass, "mult", s"(L$RationalClass;)L$RationalClass;")
      }

    case Division(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "div", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          ch << IDIV
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "div", s"(L$BitVectorClass;)L$BitVectorClass;")
        case RealType =>
          ch << InvokeVirtual(RationalClass, "div", s"(L$RationalClass;)L$RationalClass;")
      }

    case Remainder(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "rem", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          ch << IREM
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "rem", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case Modulo(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "mod", s"(L$BigIntClass;)L$BigIntClass;")
        case Int32Type =>
          // stack: (l, r)
          ch << DUP_X1
          // stack: (r, l, r)
          ch << IREM
          // stack: (r, l % r)
          ch << SWAP << DUP_X1
          // stack: (r, l % r, r)
          ch << IADD << SWAP
          // stack: (l % r + r, r)
          ch << IREM
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "mod", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case UMinus(e) =>
      mkExpr(e, ch)
      e.getType match {
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "neg", s"()L$BigIntClass;")
        case Int32Type =>
          ch << INEG
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "neg", s"()L$BitVectorClass;")
        case RealType =>
          ch << InvokeVirtual(RationalClass, "neg", s"()L$RationalClass;")
      }

    case BVNot(e) =>
      mkExpr(e, ch)
      e.getType match {
        case Int32Type =>
          mkExpr(Int32Literal(-1), ch)
          ch << IXOR
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "not", s"()L$BitVectorClass;")
      }

    case BVAnd(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << IAND
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "and", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case BVOr(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << IOR
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "or", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case BVXor(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << IXOR
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "xor", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case BVShiftLeft(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << ISHL
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "shiftLeft", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case BVLShiftRight(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << IUSHR
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "lShiftRight", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case BVAShiftRight(l, r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      e.getType match {
        case Int32Type =>
          ch << ISHR
        case BVType(_) =>
          ch << InvokeVirtual(BitVectorClass, "aShiftRight", s"(L$BitVectorClass;)L$BitVectorClass;")
      }

    case ArrayLength(a) =>
      mkExpr(a, ch)
      if (smallArrays) {
        ch << ARRAYLENGTH
      } else {
        ch << InvokeVirtual(ArrayClass, "size", "()I")
      }

    case as @ ArraySelect(a,i) =>
      mkExpr(a, ch)
      mkExpr(i, ch)
      if (smallArrays) {
        ch << (as.getType match {
          case Untyped => throw CompilationException("Cannot compile untyped array access.")
          case CharType => CALOAD
          case Int32Type => IALOAD
          case BooleanType => BALOAD
          case _ => AALOAD
        })
      } else {
        ch << InvokeVirtual(ArrayClass, "get", s"(I)L$ObjectClass;")
        mkUnbox(as.getType, ch)
      }

    case au @ ArrayUpdated(a, i, v) =>
      if (smallArrays) {
        mkExpr(a, ch)
        ch << DUP
        ch << ARRAYLENGTH

        val storeInstr = mkNewArray(a.getType, ch)

        //srcArrary and targetArray is on the stack
        ch << DUP_X1 //insert targetArray under srcArray
        ch << Ldc(0) << SWAP //srcArray, 0, targetArray
        ch << DUP << ARRAYLENGTH //targetArray, length on stack
        ch << Ldc(0) << SWAP //final arguments: src, 0, target, 0, length
        ch << InvokeStatic("java/lang/System", "arraycopy", s"(L$ObjectClass;IL$ObjectClass;II)V")

        //targetArray remains on the stack
        ch << DUP
        mkExpr(i, ch)
        mkExpr(v, ch)
        ch << storeInstr
        //returns targetArray
      } else {
        mkExpr(a, ch)
        mkExpr(i, ch)
        mkBoxedExpr(v, ch)
        ch << InvokeVirtual(ArrayClass, "updated", s"(IL$ObjectClass;)L$ArrayClass;")
      }

    case a @ FiniteArray(elems, _) =>
      if (smallArrays) {
        ch << Ldc(elems.size)
        val storeInstr = mkNewArray(a.getType, ch)

        // Replace present elements with correct value
        for ((v, i) <- elems.zipWithIndex ) {
          ch << DUP << Ldc(i)
          mkExpr(v, ch)
          ch << storeInstr
        }
      } else {
        ch << New(ArrayClass) << DUP << Ldc(elems.size)
        ch << InvokeSpecial(ArrayClass, constructorName, "(I)V")
        for ((e,i) <- elems.zipWithIndex) {
          ch << DUP
          ch << Ldc(i)
          mkBoxedExpr(e, ch)
          ch << InvokeVirtual(ArrayClass, "insert", s"(IL$ObjectClass;)V")
        }
      }

    case a @ LargeArray(elems, default, size, base) =>
      if (smallArrays) {
        mkExpr(size, ch)

        val storeInstr = mkNewArray(a.getType, ch)
        val (varLoad, varStore) = base match {
          case ValueType() => (ILoad(_), IStore(_))
          case _ => (ALoad(_), AStore(_))
        }

        val loop = ch.getFreshLabel("array_loop")
        val loopOut = ch.getFreshLabel("array_loop_out")
        val dfltSlot = ch.getFreshVar

        mkExpr(default, ch)
        ch << (base match {
          case ValueType() => IStore(dfltSlot)
          case _ => AStore(dfltSlot)
        })

        ch << Ldc(0)
        // (array, index)
        ch << Label(loop)
        ch << DUP2 << SWAP
        // (array, index, index, array)
        ch << ARRAYLENGTH
        // (array, index, index, length)
        ch << If_ICmpGe(loopOut) << DUP2
        // (array, index, array, index)
        ch << (base match {
          case ValueType() => ILoad(dfltSlot)
          case _ => ALoad(dfltSlot)
        })
        ch << storeInstr
        ch << Ldc(1) << IADD << Goto(loop)
        ch << Label(loopOut) << POP

        for ((i,v) <- elems) {
          ch << DUP << Ldc(i)
          mkExpr(v, ch)
          ch << storeInstr
        }
      } else {
        ch << New(ArrayClass) << DUP
        mkExpr(size, ch)
        mkBoxedExpr(default, ch)
        ch << InvokeSpecial(ArrayClass, constructorName, s"(IL$ObjectClass;)V")

        for ((i,e) <- elems) {
          ch << DUP
          ch << Ldc(i)
          mkBoxedExpr(e, ch)
          ch << InvokeVirtual(ArrayClass, "insert", s"(IL$ObjectClass;)V")
        }
      }


    // Misc and boolean tests
    case Error(tpe, desc) =>
      ch << New(ErrorClass) << DUP
      ch << Ldc(desc)
      ch << InvokeSpecial(ErrorClass, constructorName, "(Ljava/lang/String;)V")
      ch << ATHROW

    case forall @ Forall(fargs, body) =>
      val id = registerForall(forall, locals.tparams)
      val args = variablesOf(forall).toSeq.sortBy(_.id.uniqueName)

      load(monitorID, ch)
      ch << Ldc(id)
      if (locals.tparams.nonEmpty) {
        load(tpsID, ch)
      } else {
        ch << Ldc(0) << NewArray.primitive("T_INT")
      }

      ch << Ldc(args.size)
      ch << NewArray(ObjectClass)

      for ((v, i) <- args.zipWithIndex) {
        ch << DUP
        ch << Ldc(i)
        mkExpr(v, ch)
        mkBox(v.tpe, ch)
        ch << AASTORE
      }

      ch << InvokeVirtual(MonitorClass, "onForallInvocation", s"(I[I[L$ObjectClass;)Z")

    case choose: Choose =>
      val id = registerChoose(choose, locals.params, locals.tparams)

      load(monitorID, ch)
      ch << Ldc(id)
      if (locals.tparams.nonEmpty) {
        load(tpsID, ch)
      } else {
        ch << Ldc(0) << NewArray.primitive("T_INT")
      }

      ch << Ldc(locals.params.size)
      ch << NewArray(ObjectClass)

      for ((vd, i) <- locals.params.zipWithIndex) {
        ch << DUP
        ch << Ldc(i)
        mkExpr(vd.toVariable, ch)
        mkBox(vd.tpe, ch)
        ch << AASTORE
      }

      ch << InvokeVirtual(MonitorClass, "onChooseInvocation", s"(I[I[L$ObjectClass;)L$ObjectClass;")

      mkUnbox(choose.getType, ch)

    case gv @ GenericValue(tp, int) =>
      val id = runtime.GenericValues.register(gv)
      ch << Ldc(id)
      ch << InvokeStatic(GenericValuesClass, "get", s"(I)L$ObjectClass;")

    case nt @ NoTree(tp @ ValueType()) =>
      mkExpr(simplestValue(tp), ch)

    case NoTree(_) =>
      ch << ACONST_NULL

    case m : MatchExpr =>
      mkExpr(matchToIfThenElse(m, assumeExhaustive = false), ch)

    case b if b.getType == BooleanType && canDelegateToMkBranch =>
      val fl = ch.getFreshLabel("boolfalse")
      val al = ch.getFreshLabel("boolafter")
      ch << Ldc(1)
      mkBranch(b, al, fl, ch, canDelegateToMkExpr = false)
      ch << Label(fl) << POP << Ldc(0) << Label(al)

    case _ => throw CompilationException("Unsupported expr " + e + " : " + e.getClass)
  }

  private[codegen] def mkLambda(lambda: Lambda, ch: CodeHandler, pre: Boolean = false)(implicit locals: Locals): Unit = {
    val vars = variablesOf(lambda).toSeq
    val freshVars = vars.map(_.freshen)

    val (l: Lambda, deps) = normalizeStructure(matchToIfThenElse(
      replaceFromSymbols((vars zip freshVars).toMap, lambda),
      assumeExhaustive = false
    ))

    val (afName, closures, tparams, consSig) = compileLambda(l, locals.params, pre = pre)
    val closureTypes = variablesOf(l).map(v => v.id -> v.tpe).toMap

    val freshLocals = locals.substitute((vars zip freshVars).map(p => p._1.id -> p._2.id).toMap)

    val newLocals = deps.foldLeft(freshLocals) { case (locals, (v, e)) =>
      mkExpr(e, ch)(locals)
      val slot = ch.getFreshVar
      ch << (v.tpe match {
        case ValueType() =>
          if (slot > 127) {
            println("Error while converting one more slot which is too much " + e)
          }
          IStore(slot)
        case _ => AStore(slot)
      })
      locals.withVar(v.id -> slot)
    }

    ch << New(afName) << DUP
    for ((id,jvmt) <- closures) {
      if (id == tpsID) {
        loadTypes(tparams, ch)
      } else {
        load(id, ch, closureTypes.get(id))(newLocals)
      }
    }
    ch << InvokeSpecial(afName, constructorName, consSig)
  }

  private[codegen] def mkNewArray(tpe: Type, ch: CodeHandler): AbstractByteCode = tpe match {
    case ArrayType(CharType) => ch << NewArray.primitive("T_CHAR"); CASTORE
    case ArrayType(Int32Type) => ch << NewArray.primitive("T_INT"); IASTORE
    case ArrayType(BooleanType) => ch << NewArray.primitive("T_BOOLEAN"); BASTORE
    case ArrayType(base) =>
      val jvmt = typeToJVM(base)
      assert(jvmt.head == 'L' && jvmt.last == ';', "Unexpected jvm type for array type " + tpe)
      val clsName = jvmt.init.tail // drop leading "L" and tailing ";"
      ch << NewArray(clsName)
      AASTORE
    case other => throw new CompilationException("Cannot construct array for non-array-type " + tpe)
  }

  // Leaves on the stack a value equal to `e`, always of a type compatible with java.lang.Object.
  private[codegen] def mkBoxedExpr(e: Expr, ch: CodeHandler)
                                  (implicit locals: Locals): Unit = e.getType match {
    case Int32Type =>
      ch << New(BoxedIntClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

    case BooleanType | UnitType =>
      ch << New(BoxedBoolClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

    case CharType =>
      ch << New(BoxedCharClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedCharClass, constructorName, "(C)V")

    case at @ ArrayType(et) if smallArrays =>
      ch << New(BoxedArrayClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedArrayClass, constructorName, s"(${typeToJVM(at)})V")

    case _ =>
      mkExpr(e, ch)
  }

  // Assumes the top of the stack contains of value of the right type, and makes it
  // compatible with java.lang.Object.
  private[codegen] def mkBox(tpe: Type, ch: CodeHandler): Unit = tpe match {
    case Int32Type =>
      ch << New(BoxedIntClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

    case BooleanType | UnitType =>
      ch << New(BoxedBoolClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

    case CharType =>
      ch << New(BoxedCharClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedCharClass, constructorName, "(C)V")

    case at @ ArrayType(et) if smallArrays =>
      ch << New(BoxedArrayClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedArrayClass, constructorName, s"(${typeToJVM(at)})V")

    case _ =>
  }

  // Assumes that the top of the stack contains a value that should be of type `tpe`, and unboxes it to the right (JVM) type.
  private[codegen] def mkUnbox(tpe: Type, ch: CodeHandler): Unit = tpe match {
    case Int32Type =>
      ch << CheckCast(BoxedIntClass) << InvokeVirtual(BoxedIntClass, "intValue", "()I")

    case BooleanType | UnitType =>
      ch << CheckCast(BoxedBoolClass) << InvokeVirtual(BoxedBoolClass, "booleanValue", "()Z")

    case CharType =>
      ch << CheckCast(BoxedCharClass) << InvokeVirtual(BoxedCharClass, "charValue", "()C")

    case adt: ADTType =>
      val (cn, _) = getADTInfo(adt.getADT.definition)
      ch << CheckCast(cn)

    case IntegerType =>
      ch << CheckCast(BigIntClass)

    case StringType =>
      ch << CheckCast(JavaStringClass)

    case RealType =>
      ch << CheckCast(RationalClass)

    case tt : TupleType =>
      ch << CheckCast(TupleClass)

    case st : SetType =>
      ch << CheckCast(SetClass)

    case mt : MapType =>
      ch << CheckCast(MapClass)

    case ft : FunctionType =>
      ch << CheckCast(LambdaClass)

    case tp : TypeParameter =>

    case tp @ ArrayType(base) =>
      if (smallArrays) {
        ch << CheckCast(BoxedArrayClass)
        base match {
          case Int32Type =>
            ch << InvokeVirtual(BoxedArrayClass, "intArray", s"()${typeToJVM(tp)}")
          case BooleanType =>
            ch << InvokeVirtual(BoxedArrayClass, "booleanArray", s"()${typeToJVM(tp)}")
          case _ =>
            ch << InvokeVirtual(BoxedArrayClass, "anyRefArray", s"()[L$ObjectClass;")
            ch << CheckCast(typeToJVM(tp))
        }
      } else {
        ch << CheckCast(ArrayClass)
      }

    case _ =>
      throw new CompilationException("Unsupported type in unboxing : " + tpe)
  }

  private[codegen] def mkArrayBox(tp: Type, ch: CodeHandler): Unit = tp match {
    case at: ArrayType if smallArrays => mkBox(at, ch)
    case _ =>
  }

  private[codegen] def mkBranch(cond: Expr, thenn: String, elze: String, ch: CodeHandler, canDelegateToMkExpr: Boolean = true)
                               (implicit locals: Locals): Unit = cond match {
    case BooleanLiteral(true) =>
      ch << Goto(thenn)

    case BooleanLiteral(false) =>
      ch << Goto(elze)

    case And(es) =>
      val fl = ch.getFreshLabel("andnext")
      mkBranch(es.head, fl, elze, ch)
      ch << Label(fl)
      mkBranch(andJoin(es.tail), thenn, elze, ch)

    case Or(es) =>
      val fl = ch.getFreshLabel("ornext")
      mkBranch(es.head, thenn, fl, ch)
      ch << Label(fl)
      mkBranch(orJoin(es.tail), thenn, elze, ch)

    case Implies(l, r) =>
      mkBranch(or(not(l), r), thenn, elze, ch)

    case Not(c) =>
      mkBranch(c, elze, thenn, ch)

    case v: Variable =>
      load(v, ch)
      ch << IfEq(elze) << Goto(thenn)

    case Equals(l,r) =>
      mkExpr(l, ch)
      mkArrayBox(l.getType, ch)

      mkExpr(r, ch)
      l.getType match {
        case ValueType() =>
          ch << If_ICmpEq(thenn) << Goto(elze)

        case _ =>
          ch << InvokeVirtual(ObjectClass, "equals", s"(L$ObjectClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case LessThan(l,r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case Int32Type | CharType =>
          ch << If_ICmpLt(thenn) << Goto(elze)
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "lessThan", s"(L$BigIntClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
        case RealType =>
          ch << InvokeVirtual(RationalClass, "lessThan", s"(L$RationalClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case GreaterThan(l,r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case Int32Type | CharType =>
          ch << If_ICmpGt(thenn) << Goto(elze)
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "greaterThan", s"(L$BigIntClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
        case RealType =>
          ch << InvokeVirtual(RationalClass, "greaterThan", s"(L$RationalClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case LessEquals(l,r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case Int32Type | CharType =>
          ch << If_ICmpLe(thenn) << Goto(elze)
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "lessEquals", s"(L$BigIntClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
        case RealType =>
          ch << InvokeVirtual(RationalClass, "lessEquals", s"(L$RationalClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case GreaterEquals(l,r) =>
      mkExpr(l, ch)
      mkExpr(r, ch)
      l.getType match {
        case Int32Type | CharType =>
          ch << If_ICmpGe(thenn) << Goto(elze)
        case IntegerType =>
          ch << InvokeVirtual(BigIntClass, "greaterEquals", s"(L$BigIntClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
        case RealType =>
          ch << InvokeVirtual(RationalClass, "greaterEquals", s"(L$RationalClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case IfExpr(c, t, e) =>
      val innerThen = ch.getFreshLabel("then")
      val innerElse = ch.getFreshLabel("else")
      mkBranch(c, innerThen, innerElse, ch)
      ch << Label(innerThen)
      mkBranch(t, thenn, elze, ch)
      ch << Label(innerElse)
      mkBranch(e, thenn, elze, ch)

    case cci @ IsInstanceOf(adt, e) =>
      mkExpr(cci, ch)
      ch << IfEq(elze) << Goto(thenn)

    case other if canDelegateToMkExpr =>
      mkExpr(other, ch, canDelegateToMkBranch = false)
      ch << IfEq(elze) << Goto(thenn)

    case other => throw CompilationException("Unsupported branching expr. : " + other)
  }

  private def load(v: Variable, ch: CodeHandler)(implicit locals: Locals): Unit = load(v.id, ch, Some(v.tpe))

  private def load(id: Identifier, ch: CodeHandler, tpe: Option[Type] = None)(implicit locals: Locals): Unit = {
    locals.varToArg(id) match {
      case Some(slot) =>
        ch << ALoad(1) << Ldc(slot) << AALOAD
        tpe.foreach(tpe => mkUnbox(tpe, ch))
      case None => locals.varToField(id) match {
        case Some((afName, nme, tpe)) =>
          ch << ALoad(0) << GetField(afName, nme, tpe)
        case None => locals.varToLocal(id) match {
          case Some(slot) =>
            ch << (tpe match {
              case Some(ValueType()) => ILoad(slot)
              case _ => ALoad(slot)
            })
          case None => throw CompilationException("Unknown variable : " + id)
        }
      }
    }
  }

  def compileADTSort(sort: ADTSort): Unit = {
    val cName = defToJVMName(sort)
    val cf = getClass(sort)

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_ABSTRACT
    ).asInstanceOf[U2])

    cf.addInterface(ADTClass)

    // add special monitor for method invocations
    if (doInstrument) {
      val fh = cf.addField("I", instrumentedField)
      fh.setFlags(FIELD_ACC_PUBLIC)
    }

    // definition of the constructor
    locally {
      val constrParams = Seq(monitorID -> s"L$MonitorClass;")

      val newLocs = NoLocals.withVars {
        constrParams.map(_._1).zipWithIndex.toMap.mapValues(_ + 1)
      }

      val cch = cf.addConstructor(constrParams.map(_._2) : _*).codeHandler

      // Call parent constructor
      cch << ALoad(0)
      // Call constructor of java.lang.Object
      cch << InvokeSpecial(ObjectClass, constructorName, "()V")

      // Initialize special monitor field
      if (doInstrument) {
        cch << ALoad(0)
        cch << Ldc(0)
        cch << PutField(cName, instrumentedField, "I")
      }

      cch << RETURN
      cch.freeze
    }
  }

  /**
   * Instrument read operations
   */
  val instrumentedField = "__read"

  def instrumentedGetField(ch: CodeHandler, adt: ADTType, id: Identifier)(implicit locals: Locals): Unit = {
    val tcons = adt.getADT.toConstructor
    val cons = tcons.definition
    cons.fields.zipWithIndex.find(_._1.id == id) match {
      case Some((f, i)) =>
        val expType = tcons.fields(i).tpe

        val cName = defToJVMName(cons)
        if (doInstrument) {
          ch << DUP << DUP
          ch << GetField(cName, instrumentedField, "I")
          ch << Ldc(1)
          ch << Ldc(i)
          ch << ISHL
          ch << IOR
          ch << PutField(cName, instrumentedField, "I")
        }
        ch << GetField(cName, f.id.name, typeToJVM(f.tpe))

        f.tpe match {
          case _: TypeParameter =>
            mkUnbox(expType, ch)
          case _ =>
        }
      case None =>
        throw CompilationException("Unknown field: "+cons.id.name+"."+id)
    }
  }

  def compileADTConstructor(cons: ADTConstructor) {
    val cName = defToJVMName(cons)
    val pName = cons.sort.map(id => defToJVMName(getADT(id)))

    // An instantiation of cons with its own type parameters
    val adt = cons.typed.toType

    val cf = getClass(cons)

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    if (cons.sort.isEmpty) {
      cf.addInterface(ADTClass)
    }

    // Case class parameters
    val fieldsTypes = cons.fields.map(vd => (vd.id, typeToJVM(vd.tpe)))
    val tpeParam = if (cons.tparams.isEmpty) Seq() else Seq(tpsID -> "[I")
    val constructorArgs = (monitorID -> s"L$MonitorClass;") +: (tpeParam ++ fieldsTypes)

    val newLocs = NoLocals.withFields(constructorArgs.map {
      case (id, jvmt) => (id, (cName, id.name, jvmt))
    }.toMap)

    locally {
      // definition of the constructor
      for ((id, jvmt) <- constructorArgs) {
        val fh = cf.addField(jvmt, id.name)
        fh.setFlags((
          FIELD_ACC_PUBLIC |
          FIELD_ACC_FINAL
        ).asInstanceOf[U2])
      }

      if (doInstrument) {
        val fh = cf.addField("I", instrumentedField)
        fh.setFlags(FIELD_ACC_PUBLIC)
      }

      val cch = cf.addConstructor(constructorArgs.map(_._2) : _*).codeHandler

      if (doInstrument) {
        cch << ALoad(0)
        cch << Ldc(0)
        cch << PutField(cName, instrumentedField, "I")
      }

      var c = 1
      for ((id, jvmt) <- constructorArgs) {
        cch << ALoad(0)
        cch << (jvmt match {
          case "I" | "Z" => ILoad(c)
          case _ => ALoad(c)
        })
        cch << PutField(cName, id.name, jvmt)
        c += 1
      }

      // Call parent constructor AFTER initializing case class parameters
      if (cons.sort.isDefined) {
        cch << ALoad(0)
        cch << ALoad(1)
        cch << InvokeSpecial(pName.get, constructorName, s"(L$MonitorClass;)V")
      } else {
        // Call constructor of java.lang.Object
        cch << ALoad(0)
        cch << InvokeSpecial(ObjectClass, constructorName, "()V")
      }

      cch << RETURN
      cch.freeze
    }

    locally {
      val pnm = cf.addMethod("I", "__getRead")
      pnm.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val pnch = pnm.codeHandler

      pnch << ALoad(0) << GetField(cName, instrumentedField, "I") << IRETURN

      pnch.freeze
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
      val pem = cf.addMethod(s"[L$ObjectClass;", "productElements")
      pem.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val pech = pem.codeHandler

      pech << Ldc(cons.fields.size)
      pech << NewArray(ObjectClass)

      for ((f, i) <- cons.fields.zipWithIndex) {
        pech << DUP
        pech << Ldc(i)
        pech << ALoad(0)
        instrumentedGetField(pech, adt, f.id)(newLocs)
        mkBox(f.tpe, pech)
        pech << AASTORE
      }

      pech << ARETURN
      pech.freeze
    }

    // definition of equals
    locally {
      val emh = cf.addMethod("Z", "equals", s"L$ObjectClass;")
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
      if (cons.fields.nonEmpty) {
        ech << ALoad(1) << CheckCast(cName) << AStore(castSlot)

        for (vd <- cons.fields) {
          ech << ALoad(0)
          instrumentedGetField(ech, adt, vd.id)(newLocs)
          mkArrayBox(vd.tpe, ech)

          ech << ALoad(castSlot)
          instrumentedGetField(ech, adt, vd.id)(newLocs)

          vd.tpe match {
            case ValueType() =>
              ech << If_ICmpNe(notEq)

            case ot =>
              ech << InvokeVirtual(ObjectClass, "equals", s"(L$ObjectClass;)Z") << IfEq(notEq)
          }
        }
      }

      ech << Ldc(1) << IRETURN << Label(notEq) << Ldc(0) << IRETURN
      ech.freeze
    }

    // definition of hashcode
    locally {
      val hashFieldName = "$leon$hashCode"
      cf.addField("I", hashFieldName).setFlags(FIELD_ACC_PRIVATE)
      val hmh = cf.addMethod("I", "hashCode", "")
      hmh.setFlags((
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
      ).asInstanceOf[U2])

      val hch = hmh.codeHandler

      val wasNotCached = hch.getFreshLabel("wasNotCached")

      hch << ALoad(0) << GetField(cName, hashFieldName, "I") << DUP
      hch << IfEq(wasNotCached)
      hch << IRETURN
      hch << Label(wasNotCached) << POP
      hch << ALoad(0) << InvokeVirtual(cName, "productElements", s"()[L$ObjectClass;")
      hch << ALoad(0) << InvokeVirtual(cName, "productName", "()Ljava/lang/String;")
      hch << InvokeVirtual("java/lang/String", "hashCode", "()I")
      hch << InvokeStatic(HashingClass, "arrayHash", s"([L$ObjectClass;I)I") << DUP
      hch << ALoad(0) << SWAP << PutField(cName, hashFieldName, "I")
      hch << IRETURN

      hch.freeze
    }

  }
}
