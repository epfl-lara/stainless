/* Copyright 2009-2021 EPFL, Lausanne */

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
import scala.collection.concurrent.{TrieMap => ConcurrentMap}

case class CompilationException(msg: String) extends Exception(msg)

object optInstrumentFields extends inox.FlagOptionDef("instrument", false)
object optSmallArrays extends inox.FlagOptionDef("small-arrays", false)

trait CodeGeneration { self: CompilationUnit =>
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import program.trees.exprOps._

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
  private[codegen] val BoxedByteClass            = "java/lang/Byte"
  private[codegen] val BoxedShortClass           = "java/lang/Short"
  private[codegen] val BoxedIntClass             = "java/lang/Integer"
  private[codegen] val BoxedLongClass            = "java/lang/Long"
  private[codegen] val BoxedBoolClass            = "java/lang/Boolean"
  private[codegen] val BoxedCharClass            = "java/lang/Character"
  private[codegen] val BoxedArrayClass           = "stainless/codegen/runtime/BoxedArray"

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

  private[codegen] val HashingClass              = "java/util/Arrays"

  def idToSafeJVMName(id: Identifier) = {
    scala.reflect.NameTransformer.encode(id.uniqueName).replaceAll("\\.", "\\$")
  }

  private def defToJVMName(id: Identifier): String = "Stainless$CodeGen$Def$" + idToSafeJVMName(id)
  def defSortToJVMName(sort: ADTSort): String = defToJVMName(sort.id)
  def defConsToJVMName(cons: ADTConstructor): String = defToJVMName(cons.id)
  def defFnToJVMName(fd: FunDef): String = defToJVMName(fd.id)

  private[this] val sortClassFiles : MutableMap[ADTSort, ClassFile] = MutableMap.empty
  private[this] val classToSort    : MutableMap[String, ADTSort]    = MutableMap.empty

  def getClassSort(sort: ADTSort): ClassFile = synchronized(sortClassFiles.getOrElse(sort, {
    val cf = new ClassFile(defSortToJVMName(sort), None)
    classToSort += cf.className -> sort
    sortClassFiles(sort) = cf
    cf
  }))

  private[this] val consClassFiles : MutableMap[ADTConstructor, ClassFile] = MutableMap.empty
  private[this] val classToCons    : MutableMap[String, ADTConstructor]    = MutableMap.empty

  def getClassCons(cons: ADTConstructor): ClassFile = synchronized(consClassFiles.getOrElse(cons, {
    val cf = new ClassFile(defConsToJVMName(cons), Some(defSortToJVMName(cons.getSort)))
    classToCons += cf.className -> cons
    consClassFiles(cons) = cf
    cf
  }))

  private[this] lazy val static = new ClassFile("<static>", None)

  protected def compile(): Seq[ClassFile] = {
    for (sort <- sorts.values) {
      compileADTSort(sort)
      for (cons <- sort.constructors) compileADTConstructor(cons)
    }

    for (fd <- functions.values) {
      compileFunDef(fd, static)
    }

    (sortClassFiles.values.toSeq ++ consClassFiles.values) :+ static
  }

  protected def jvmClassNameToSort(className: String): Option[ADTSort] = classToSort.get(className)
  protected def jvmClassNameToCons(className: String): Option[ADTConstructor] = classToCons.get(className)

  private[this] val sortInfos: ConcurrentMap[ADTSort, (String, String)] = ConcurrentMap.empty
  private[this] val consInfos: ConcurrentMap[ADTConstructor, (String, String)] = ConcurrentMap.empty

  protected def getSortInfo(sort: ADTSort): (String, String) = sortInfos.getOrElse(sort, {
    val tpeParam = if (sort.tparams.isEmpty) "" else "[I"
    val res = (getClassSort(sort).className, "(L"+MonitorClass+";" + tpeParam + ")V")
    sortInfos(sort) = res
    res
  })

  protected def getConsInfo(cons: ADTConstructor): (String, String) = consInfos.getOrElse(cons, {
    val tpeParam = if (cons.getSort.tparams.isEmpty) "" else "[I"
    val sig = "(L"+MonitorClass+";" + tpeParam + cons.fields.map(f => typeToJVM(f.getType)).mkString("") + ")V"
    val res = (getClassCons(cons).className, sig)
    consInfos(cons) = res
    res
  })

  private[this] val funDefInfos: ConcurrentMap[FunDef, (String, String, String)] = ConcurrentMap.empty

  protected def getFunDefInfo(fd: FunDef): (String, String, String) = funDefInfos.getOrElse(fd, {
    val sig = "(L"+MonitorClass+";" +
      (if (fd.tparams.nonEmpty) "[I" else "") +
      fd.params.map(a => typeToJVM(a.getType)).mkString("") + ")" + typeToJVM(fd.getType)

    val res = (static.className, idToSafeJVMName(fd.id), sig)
    funDefInfos(fd) = res
    res
  })

  /**
    * JvmIType is for type that can use (most of) JVM bytecode starting with `i` (e.g. iconst, iload, ireturn, ...)
    *
    * Long is not a JvmIType!
    */
  protected object JvmIType {
    def unapply(tp: Type): Boolean = tp match {
      case Int8Type() | Int16Type() | Int32Type() | BooleanType() | CharType() | UnitType() => true
      case _ => false
    }
  }

  /** Return the respective JVM type from a Stainless type */
  def typeToJVM(tpe: Type) : String = tpe.getType match {
    case Int8Type()  => "B"
    case Int16Type() => "S"
    case Int32Type() => "I"
    case Int64Type() => "J"
    case BVType(_, _) => "L" + BitVectorClass + ";"

    case BooleanType() => "Z"

    case CharType() => "C"

    case UnitType() => "Z"

    case adt: ADTType =>
      val (n, _) = getSortInfo(adt.getSort.definition)
      s"L$n;"

    case _ : TupleType =>
      "L" + TupleClass + ";"

    case _ : SetType =>
      "L" + SetClass + ";"

    case _ : BagType =>
      "L" + BagClass + ";"

    case _ : MapType =>
      "L" + MapClass + ";"

    case IntegerType() =>
      "L" + BigIntClass + ";"

    case RealType() =>
      "L" + RationalClass + ";"

    case _ : FunctionType =>
      "L" + LambdaClass + ";"

    case ArrayType(base) =>
      if (smallArrays) "[" + typeToJVM(base)
      else "L" + ArrayClass + ";"

    case _: TypeParameter =>
      "L" + ObjectClass + ";"

    case StringType() =>
      "L" + JavaStringClass + ";"

    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  /** Return the respective boxed JVM type from a Stainless type */
  def typeToJVMBoxed(tpe: Type) : String = tpe match {
    case Int8Type()                 => s"L$BoxedByteClass;"
    case Int16Type()                => s"L$BoxedShortClass;"
    case Int32Type()                => s"L$BoxedIntClass;"
    case Int64Type()                => s"L$BoxedLongClass;"
    case BooleanType() | UnitType() => s"L$BoxedBoolClass;"
    case CharType()                 => s"L$BoxedCharClass;"
    case other                      => typeToJVM(other)
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
      typeToJVM(funDef.getType),
      mn,
      realParams : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL  |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val newMapping: Map[Identifier, Int] = {
      var nextFreeSlot = 0
      def getSlot(isLong: Boolean) = {
        val slot = nextFreeSlot
        nextFreeSlot += (if (isLong) 2 else 1) // Longs take more room!
        slot
      }

      val monitor = monitorID -> getSlot(false)
      val tpsOpt = if (funDef.tparams.nonEmpty) Some(tpsID -> getSlot(false)) else None
      val params = funDef.params map { p =>
        val isLong = p.getType match {
          case Int64Type() => true
          case _ => false
        }
        p.id -> getSlot(isLong)
      }

      Seq(monitor) ++ tpsOpt ++ params
    }.toMap

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
      loadImpl(monitorID, ch)(using locals)
      ch << InvokeVirtual(MonitorClass, "onInvocation", "()V")
    }

    mkExpr(body, ch)(using locals)

    funDef.getType match {
      case JvmIType() =>
        ch << IRETURN
      case Int64Type() =>
        ch << LRETURN
      case _ =>
        ch << ARETURN
    }

    ch.freeze
  }

  private[this] val lambdaClasses = new Bijection[Lambda, String]

  protected def jvmClassNameToLambda(className: String): Option[Lambda] = lambdaClasses.getA(className)

  private val typeParams: ListBuffer[TypeParameter] = new ListBuffer[TypeParameter]

  protected def compileLambda(l: Lambda, params: Seq[ValDef]):
                             (String, Seq[(Identifier, String)], Seq[TypeParameter], String) = synchronized {
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

    class LambdaNormalizer(override val s: program.trees.type, override val t: program.trees.type)
      extends transformers.ConcreteTreeTransformer(s, t) {

      def this() = this(program.trees, program.trees)

      override def transform(tpe: Type): Type = tpe match {
        case tp: TypeParameter => subst(tp)
        case _ => super.transform(tpe)
      }
    }

    val normalizer = new LambdaNormalizer
    val lambda = normalizer.transform(l).asInstanceOf[Lambda]
    val (tparams, tps) = tpSubst.toSeq.sortBy(_._2.id.id).unzip

    val closedVars = variablesOf(lambda).toSeq.sortBy(_.id.uniqueName)

    val closuresWithoutMonitor = closedVars.map(v => v -> typeToJVM(v.getType))
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
              case "B" | "S" | "I" | "Z" => ILoad(c)
              case "J" => LLoad(c)
              case _ => ALoad(c)
            })
            cch << PutField(afName, id.uniqueName, jvmt)
            c += 1
          }

          cch << RETURN
          cch.freeze
        }

        val argMapping = lambda.params.zipWithIndex.map { case (v, i) => v.id -> i }.toMap
        val closureMapping = closures.map { case (id, jvmt) => id -> (afName, id.uniqueName, jvmt) }.toMap
        val newLocals = NoLocals.withArgs(argMapping).withFields(closureMapping)
          .withParameters(params ++ l.params).withTypeParameters(tps)

        locally {
          val apm = cf.addMethod(s"L$ObjectClass;", "apply", s"[L$ObjectClass;")

          apm.setFlags((
            METHOD_ACC_PUBLIC |
            METHOD_ACC_FINAL
          ).asInstanceOf[U2])

          val apch = apm.codeHandler

          mkBoxedExpr(lambda.body, apch)(using newLocals)

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
          val castSlot = ech.getFreshVar(1) // 1 byte for references

          // If references are equal, trees are equal.
          ech << ALoad(0) << ALoad(1) << If_ACmpNe(notRefEq) << Ldc(1) << IRETURN << Label(notRefEq)

          // We check the type (this also checks against null)....
          ech << ALoad(1) << InstanceOf(afName) << IfEq(notEq)

          // ...finally, we compare fields one by one, shortcircuiting on disequalities.
          if (closures.nonEmpty) {
            ech << ALoad(1) << CheckCast(afName) << AStore(castSlot)

            for ((v, jvmt) <- closuresWithoutMonitor) {
              ech << ALoad(0) << GetField(afName, v.id.uniqueName, jvmt)
              mkArrayBox(v.getType, ech)

              ech << ALoad(castSlot) << GetField(afName, v.id.uniqueName, jvmt)

              v.getType match {
                case JvmIType() =>
                  ech << If_ICmpNe(notEq)

                case Int64Type() => ???

                case ot =>
                  ech << InvokeVirtual(ObjectClass, "equals", s"(L$ObjectClass;)Z") << IfEq(notEq)
              }
            }
          }

          ech << Ldc(1) << IRETURN << Label(notEq) << Ldc(0) << IRETURN
          ech.freeze
        }

        locally {
          val hashFieldName = "$stainless$hashCode"
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

          hch << Ldc(afName.hashCode)
          hch << Ldc(closuresWithoutMonitor.size) << NewArray(s"$ObjectClass")
          for (((v, jvmt),i) <- closuresWithoutMonitor.zipWithIndex) {
            hch << DUP << Ldc(i)
            hch << ALoad(0) << GetField(afName, v.id.uniqueName, jvmt)
            mkBox(v.getType, hch)
            hch << AASTORE
          }

          hch << InvokeStatic(HashingClass, "hashCode", s"([L$ObjectClass;)I") << IADD << DUP
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
  private def mkTuple(es: Seq[Expr], ch: CodeHandler)(using locals: Locals) : Unit = {
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

  private def loadTypes(tps: Seq[Type], ch: CodeHandler)(using locals: Locals): Unit = {
    if (tps.nonEmpty) {
      ch << Ldc(tps.size)
      ch << NewArray.primitive("T_INT")
      for ((tpe,idx) <- tps.zipWithIndex) {
        ch << DUP << Ldc(idx)

        val vars = typeOps.variablesOf(tpe)
        if (vars.nonEmpty) {
          loadImpl(monitorID, ch)
          ch << Ldc(registerType(tpe))

          ch << Ldc(vars.size) << NewArray(s"$ObjectClass")
          for ((v,idx) <- vars.toSeq.sortBy(_.id).zipWithIndex) {
            ch << DUP << Ldc(idx)
            mkBoxedExpr(v, ch)
            ch << AASTORE
          }

          ch << InvokeVirtual(MonitorClass, "typeSubstitute", s"(I[L$ObjectClass;)I")
        } else {
          ch << Ldc(registerType(tpe))
        }

        ch << IASTORE
      }

      if (locals.tparams.nonEmpty) {
        loadImpl(monitorID, ch)
        ch << SWAP

        ch << Ldc(locals.tparams.size)
        ch << NewArray.primitive("T_INT")
        for ((tpe,idx) <- locals.tparams.zipWithIndex) {
          ch << DUP << Ldc(idx) << Ldc(registerType(tpe)) << IASTORE
        }

        ch << SWAP
        loadImpl(tpsID, ch)
        ch << InvokeVirtual(MonitorClass, "typeParams", s"([I[I[I)[I")
      }
    }
  }

  private[codegen] def mkExpr(e: Expr, ch: CodeHandler, canDelegateToMkBranch: Boolean = true)
                             (using locals: Locals): Unit = e match {
    case v: Variable =>
      load(v, ch)

    case Assert(cond, oerr, body) =>
      mkExpr(IfExpr(Not(cond), Error(body.getType, oerr.getOrElse("Assertion failed @"+e.getPos)), body), ch)

    case Assume(cond, body) =>
      mkExpr(IfExpr(Not(cond), Error(body.getType, "Assumption failed @"+e.getPos), body), ch)

    case en @ Ensuring(_, _) =>
      mkExpr(en.toAssert, ch)

    case Require(pre, body) =>
      mkExpr(IfExpr(pre, body, Error(body.getType, "Precondition failed")), ch)

    case Decreases(measure, body) =>
      mkExpr(body, ch)

    case Let(vd, d, v) if vd.toVariable == v => // Optimization for local variables.
      mkExpr(d, ch)

    case Let(vd, d, Let(vd2, v, v2)) if vd.toVariable == v && vd2.toVariable == v2 => // Optimization for local variables.
      mkExpr(d, ch)

    case Let(vd,d,b) =>
      mkExpr(d, ch)
      val slot = ch.getFreshVar(typeToJVM(d.getType))
      if (slot > 127) sys.error("Error while converting one more slot which is too much " + e)
      ch << (vd.getType match {
        case JvmIType() => IStore(slot)
        case Int64Type() => LStore(slot)
        case _ => AStore(slot)
      })
      mkExpr(b, ch)(using locals.withVar(vd.id -> slot))

    case Int8Literal(v) =>
      ch << Ldc(v)

    case Int16Literal(v) =>
      ch << Ldc(v)

    case Int32Literal(v) =>
      ch << Ldc(v)

    case Int64Literal(v) =>
      ch << Ldc(v)

    case bi @ BVLiteral(signed, _, size) =>
      val value = bi.toBigInt.toString
      ch << Comment("new bv")
      ch << New(BitVectorClass) << DUP
      ch << Comment(s"init bv from signed + string + size: (L$JavaStringClass;I)V")
      ch << Ldc(if (signed) 1 else 0) << Ldc(value) << Ldc(size)
      ch << InvokeSpecial(BitVectorClass, constructorName, s"(ZL$JavaStringClass;I)V")

    case CharLiteral(v) =>
      ch << Ldc(v)

    case BooleanLiteral(v) =>
      ch << Ldc(if(v) 1 else 0)

    case UnitLiteral() =>
      ch << Ldc(1)

    case StringLiteral(v) =>
      ch << Ldc(v)

    case IntegerLiteral(v) =>
      ch << Comment(s"New BigInt(LString;)V")
      ch << New(BigIntClass) << DUP
      ch << Ldc(v.toString)
      ch << InvokeSpecial(BigIntClass, constructorName, s"(L$JavaStringClass;)V")

    case FractionLiteral(n, d) =>
      ch << New(RationalClass) << DUP
      ch << Ldc(n.toString)
      ch << Ldc(d.toString)
      ch << InvokeSpecial(RationalClass, constructorName, s"(L$JavaStringClass;L$JavaStringClass;)V")

    case adt @ SizedADT(id, tps, as, _) =>
      mkExpr(ADT(id, tps, as), ch, canDelegateToMkBranch)

    case adt @ ADT(id, tps, as) =>
      val tcons = adt.getConstructor
      val cons = tcons.definition
      val (adtName, adtApplySig) = getConsInfo(cons)
      ch << New(adtName) << DUP
      loadImpl(monitorID, ch)
      loadTypes(tps, ch)

      for ((a, vd) <- as zip cons.fields) {
        vd.getType match {
          case _: TypeParameter =>
            mkBoxedExpr(a, ch)
          case _ =>
            mkExpr(a, ch)
        }
      }
      ch << InvokeSpecial(adtName, constructorName, adtApplySig)

      // check invariant (if it exists)
      if (!ignoreContracts && cons.getSort.hasInvariant) {
        ch << DUP

        val tfd = tcons.sort.invariant.get
        val (cn, mn, ms) = getFunDefInfo(tfd.fd)

        loadImpl(monitorID, ch)
        ch << SWAP // stack: (monitor, adt)

        if (tfd.tps.nonEmpty) {
          loadTypes(tfd.tps, ch)
          ch << SWAP // stack: (monitor, tps, adt)
        }

        ch << InvokeStatic(cn, mn, ms)

        val ok = ch.getFreshLabel("invariant_ok")
        ch << IfNe(ok)
        mkExpr(Error(BooleanType(), "ADT invariant failed @" + e.getPos), ch)
        ch << Label(ok)
      }

    case IsConstructor(e, id) =>
      val (ccName, _) = getConsInfo(getConstructor(id))
      mkExpr(e, ch)
      ch << InstanceOf(ccName)

    case sel @ ADTSelector(e, sid) =>
      mkExpr(e, ch)
      val tcons = sel.constructor
      val (ccName, _) = getConsInfo(tcons.definition)
      ch << CheckCast(ccName)
      instrumentedGetField(ch, tcons, sid)

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

      loadImpl(monitorID, ch)
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

      (tfd.fd.getType, tfd.getType) match {
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

    case lambda: Lambda =>
      mkLambda(lambda, ch)

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
    case Plus(l, r)      => mkArithmeticBinary(l, r, ch, IADD, LADD, "add", bvOnly = false)
    case Minus(l, r)     => mkArithmeticBinary(l, r, ch, ISUB, LSUB, "sub", bvOnly = false)
    case Times(l, r)     => mkArithmeticBinary(l, r, ch, IMUL, LMUL, "mult", bvOnly = false)
    case Division(l, r)  => mkArithmeticBinary(l, r, ch, IDIV, LDIV, "div", bvOnly = false)
    case Remainder(l, r) => mkArithmeticBinary(l, r, ch, IREM, LREM, "rem", bvOnly = false)

    case Modulo(l, r) =>
      ch << Comment(s"Modulo")
      mkExpr(l, ch)
      mkExpr(r, ch)

      val op = "mod"
      l.getType match {
        case IntegerType() =>
          val opSign = s"(L$BigIntClass;)L$BigIntClass;"
          ch << Comment(s"[binary, bigint] Calling $op: $opSign")
          ch << InvokeVirtual(BigIntClass, op, opSign)

        case t @ (Int8Type() | Int16Type() | Int32Type() | Int64Type()) =>
          // NOTE Here we always rely on BitVector's implementation of modulo.

          val (param, extract, size) = t match {
            case Int8Type()  => ("B", "toByte", 8)
            case Int16Type() => ("S", "toShort", 16)
            case Int32Type() => ("I", "toInt", 32)
            case Int64Type() => ("J", "toLong", 64)
            case _ => sys.error("Unreachable") // To silence false positive warning
          }

          // stack: (l, r)
          mkNewBV(ch, param, size)
          // stack: (l, bvr)
          if (param == "J") ch << DUP_X2 << POP
          else ch << SWAP
          mkNewBV(ch, param, size)
          ch << SWAP
          // stack: (bvl, bvr)
          val signOp = s"(L$BitVectorClass;)L$BitVectorClass;"
          ch << Comment(s"[binary, BVType(true, $size)] invoke $op on BitVector: $signOp")
          ch << InvokeVirtual(BitVectorClass, op, signOp)
          // stack: (bv)
          val signExtract = s"()$param"
          ch << Comment(s"[binary, BVType(true, $size)] invoke $extract on BitVector: $signExtract")
          ch << InvokeVirtual(BitVectorClass, extract, signExtract)

        case BVType(_, _) =>
          val opSign = s"(L$BitVectorClass;)L$BitVectorClass;"
          ch << Comment(s"[binary, bitvector] Calling $op: $opSign")
          ch << InvokeVirtual(BitVectorClass, op, opSign)
      }

    case UMinus(e) => mkArithmeticUnary(e, ch, INEG, LNEG, "neg", bvOnly = false)
    case BVNot(e) =>
      val iopGen: AbstractByteCodeGenerator = { ch =>
        mkExpr(Int32Literal(-1), ch)
        ch << IXOR
      }

      val lopGen: AbstractByteCodeGenerator = { ch =>
        mkExpr(Int64Literal(-1), ch)
        ch << LXOR
      }

      mkArithmeticUnaryImpl(e, ch, iopGen, lopGen, "not", bvOnly = true)

    case BVAnd(l, r) => mkArithmeticBinary(l, r, ch, IAND, LAND, "and", bvOnly = true)
    case BVOr(l, r)  => mkArithmeticBinary(l, r, ch, IOR, LOR, "or", bvOnly = true)
    case BVXor(l, r) => mkArithmeticBinary(l, r, ch, IXOR, LXOR, "xor", bvOnly = true)
    case BVShiftLeft(l, r)   => mkBVShift(l, r, ch, ISHL,  LSHL,  "shiftLeft")
    case BVLShiftRight(l, r) => mkBVShift(l, r, ch, IUSHR, LUSHR, "lShiftLeft")
    case BVAShiftRight(l, r) => mkBVShift(l, r, ch, ISHR,  LSHR,  "aShiftRight")

    case BVNarrowingCast(e, to) =>
      mkExpr(e, ch)
      val from = e.getType
      (from, to) match {
        case (Int16Type(), Int8Type() ) => ch << I2B
        case (Int32Type(), Int8Type() ) => ch << I2B
        case (Int32Type(), Int16Type()) => ch << I2S
        case (Int64Type(), Int8Type() ) => ch << L2I << I2B
        case (Int64Type(), Int16Type()) => ch << L2I << I2S
        case (Int64Type(), Int32Type()) => ch << L2I
        case (BVType(_, s), BVType(_, t)) if s == t => ch << NOP
        case (from, to) => mkBVCast(from, to, ch)
      }

    case BVWideningCast(e, to) =>
      mkExpr(e, ch)
      val from = e.getType
      (from, to) match {
        case (Int8Type(),  Int16Type()) => ch << I2S
        case (Int8Type(),  Int32Type()) => ch << NOP // already an int
        case (Int8Type(),  Int64Type()) => ch << I2L
        case (Int16Type(), Int32Type()) => ch << NOP // already an int
        case (Int16Type(), Int64Type()) => ch << I2L
        case (Int32Type(), Int64Type()) => ch << I2L
        case (BVType(_, s), BVType(_, t)) if s == t => ch << NOP
        case (from, to) => mkBVCast(from, to, ch)
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
          case CharType() => CALOAD
          case Int8Type() => BALOAD
          case Int16Type() => SALOAD
          case Int32Type() => IALOAD
          case Int64Type() => LALOAD
          case BooleanType() => BALOAD
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

        val loop = ch.getFreshLabel("array_loop")
        val loopOut = ch.getFreshLabel("array_loop_out")
        val dfltSlot = ch.getFreshVar(typeToJVM(base))

        mkExpr(default, ch)
        ch << (base match {
          case JvmIType() => IStore(dfltSlot)
          case Int64Type() => LStore(dfltSlot)
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
          case JvmIType() => ILoad(dfltSlot)
          case Int64Type() => LLoad(dfltSlot)
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
      ch << InvokeSpecial(ErrorClass, constructorName, s"(L$JavaStringClass;)V")
      ch << ATHROW

    case forall @ Forall(fargs, body) =>
      val id = registerForall(forall, locals.tparams)
      val args = variablesOf(forall).toSeq.sortBy(_.id.uniqueName)

      loadImpl(monitorID, ch)
      ch << Ldc(id)
      if (locals.tparams.nonEmpty) {
        loadImpl(tpsID, ch)
      } else {
        ch << Ldc(0) << NewArray.primitive("T_INT")
      }

      ch << Ldc(args.size)
      ch << NewArray(ObjectClass)

      for ((v, i) <- args.zipWithIndex) {
        ch << DUP
        ch << Ldc(i)
        mkExpr(v, ch)
        mkBox(v.getType, ch)
        ch << AASTORE
      }

      ch << InvokeVirtual(MonitorClass, "onForallInvocation", s"(I[I[L$ObjectClass;)Z")

    case choose: Choose =>
      val id = registerChoose(choose, locals.params, locals.tparams)

      loadImpl(monitorID, ch)
      ch << Ldc(id)
      if (locals.tparams.nonEmpty) {
        loadImpl(tpsID, ch)
      } else {
        ch << Ldc(0) << NewArray.primitive("T_INT")
      }

      ch << Ldc(locals.params.size)
      ch << NewArray(ObjectClass)

      for ((vd, i) <- locals.params.zipWithIndex) {
        ch << DUP
        ch << Ldc(i)
        mkExpr(vd.toVariable, ch)
        mkBox(vd.getType, ch)
        ch << AASTORE
      }

      ch << InvokeVirtual(MonitorClass, "onChooseInvocation", s"(I[I[L$ObjectClass;)L$ObjectClass;")

      mkUnbox(choose.getType, ch)

    case gv @ GenericValue(tp, int) =>
      val id = runtime.GenericValues.register(gv)
      ch << Ldc(id)
      ch << InvokeStatic(GenericValuesClass, "get", s"(I)L$ObjectClass;")

    case nt @ NoTree(tp @ (JvmIType() | Int64Type())) =>
      mkExpr(simplestValue(tp), ch)

    case NoTree(_) =>
      ch << ACONST_NULL

    case m: MatchExpr =>
      mkExpr(matchToIfThenElse(m, assumeExhaustive = false), ch)

    case p: Passes =>
      mkExpr(p.asConstraint, ch)

    case b if b.getType == BooleanType() && canDelegateToMkBranch =>
      val fl = ch.getFreshLabel("boolfalse")
      val al = ch.getFreshLabel("boolafter")
      ch << Ldc(1)
      mkBranch(b, al, fl, ch, canDelegateToMkExpr = false)
      ch << Label(fl) << POP << Ldc(0) << Label(al)

    case m: Max =>
      mkExpr(maxToIfThenElse(m), ch)

    case Annotated(body, _) =>
      mkExpr(body, ch)

    case _ => throw CompilationException("Unsupported expr " + e + " : " + e.getClass)
  }

  private[codegen] def mkLambda(lambda: Lambda, ch: CodeHandler)(using locals: Locals): Unit = {
    val vars = variablesOf(lambda).toSeq
    val freshVars = vars.map(_.freshen)

    val (l: Lambda, deps) = normalizeStructure(matchToIfThenElse(
      replaceFromSymbols((vars zip freshVars).toMap, lambda),
      assumeExhaustive = false
    ))

    val (afName, closures, tparams, consSig) = compileLambda(l, locals.params)
    val closureTypes = variablesOf(l).map(v => v.id -> v.getType).toMap

    val freshLocals = locals.substitute((vars zip freshVars).map(p => p._1.id -> p._2.id).toMap)

    val depsMap = deps.map(p => p._1.id -> p._2).toMap
    var depsSlot = Map.empty[Identifier, Int]
    def mkExprWithDeps(e: Expr): Unit = {
      val vars = variablesOf(e).map(_.id).filter(depsMap contains _)
      val depLocals = vars.foldLeft(freshLocals)((locals, id) => depsSlot.get(id) match {
        case Some(slot) => locals.withVar(id -> slot)
        case None =>
          val dep = depsMap(id)
          mkExprWithDeps(dep)
          val slot = ch.getFreshVar(typeToJVM(dep.getType))
          ch << (dep.getType match {
            case JvmIType() => IStore(slot)
            case Int64Type() => LStore(slot)
            case _ => AStore(slot)
          })
          depsSlot += id -> slot
          locals.withVar(id -> slot)
      })
      mkExpr(e, ch)(using depLocals)
    }

    ch << New(afName) << DUP
    for ((id,jvmt) <- closures) {
      if (id == tpsID) {
        loadTypes(tparams, ch)
      } else if (depsMap contains id) {
        mkExprWithDeps(depsMap(id))
      } else {
        loadImpl(id, ch, closureTypes.get(id))(using freshLocals)
      }
    }
    ch << InvokeSpecial(afName, constructorName, consSig)
  }

  private[codegen] def mkNewArray(tpe: Type, ch: CodeHandler): AbstractByteCode = tpe match {
    case ArrayType(CharType()) => ch << NewArray.primitive("T_CHAR"); CASTORE
    case ArrayType(Int8Type()) => ch << NewArray.primitive("T_BYTE"); BASTORE
    case ArrayType(Int16Type()) => ch << NewArray.primitive("T_SHORT"); SASTORE
    case ArrayType(Int32Type()) => ch << NewArray.primitive("T_INT"); IASTORE
    case ArrayType(Int64Type()) => ch << NewArray.primitive("T_LONG"); LASTORE
    case ArrayType(BooleanType()) => ch << NewArray.primitive("T_BOOLEAN"); BASTORE
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
                                  (using locals: Locals): Unit = e.getType match {
    case Int8Type() =>
      ch << New(BoxedByteClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedByteClass, constructorName, "(B)V")

    case Int16Type() =>
      ch << New(BoxedShortClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedShortClass, constructorName, "(S)V")

    case Int32Type() =>
      ch << New(BoxedIntClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

    case Int64Type() =>
      ch << New(BoxedLongClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedLongClass, constructorName, "(J)V")

    case BooleanType() | UnitType() =>
      ch << New(BoxedBoolClass) << DUP
      mkExpr(e, ch)
      ch << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

    case CharType() =>
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
    case Int8Type() =>
      ch << New(BoxedByteClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedByteClass, constructorName, "(B)V")

    case Int16Type() =>
      ch << New(BoxedShortClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedShortClass, constructorName, "(S)V")

    case Int32Type() =>
      ch << New(BoxedIntClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

    case Int64Type() =>
      ch << New(BoxedLongClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedLongClass, constructorName, "(J)V")

    case BooleanType() | UnitType() =>
      ch << New(BoxedBoolClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

    case CharType() =>
      ch << New(BoxedCharClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedCharClass, constructorName, "(C)V")

    case at @ ArrayType(et) if smallArrays =>
      ch << New(BoxedArrayClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedArrayClass, constructorName, s"(${typeToJVM(at)})V")

    case _ =>
  }

  // Assumes that the top of the stack contains a value that should be of type `tpe`, and unboxes it to the right (JVM) type.
  private[codegen] def mkUnbox(tpe: Type, ch: CodeHandler): Unit = tpe match {
    case Int8Type() =>
      ch << CheckCast(BoxedByteClass) << InvokeVirtual(BoxedByteClass, "byteValue", "()B")

    case Int16Type() =>
      ch << CheckCast(BoxedShortClass) << InvokeVirtual(BoxedShortClass, "shortValue", "()S")

    case Int32Type() =>
      ch << CheckCast(BoxedIntClass) << InvokeVirtual(BoxedIntClass, "intValue", "()I")

    case Int64Type() =>
      ch << CheckCast(BoxedLongClass) << InvokeVirtual(BoxedLongClass, "longValue", "()J")

    case BooleanType() | UnitType() =>
      ch << CheckCast(BoxedBoolClass) << InvokeVirtual(BoxedBoolClass, "booleanValue", "()Z")

    case CharType() =>
      ch << CheckCast(BoxedCharClass) << InvokeVirtual(BoxedCharClass, "charValue", "()C")

    case adt: ADTType =>
      val (cn, _) = getSortInfo(adt.getSort.definition)
      ch << CheckCast(cn)

    case IntegerType() =>
      ch << CheckCast(BigIntClass)

    case StringType() =>
      ch << CheckCast(JavaStringClass)

    case RealType() =>
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
          case Int8Type() | Int16Type() | Int64Type() => sys.error("NOT IMPLEMENTED")
          case Int32Type() =>
            ch << InvokeVirtual(BoxedArrayClass, "intArray", s"()${typeToJVM(tp)}")
          case BooleanType() =>
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
                               (using locals: Locals): Unit = cond match {
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
        case JvmIType() =>
          ch << If_ICmpEq(thenn) << Goto(elze)

        case Int64Type() =>
          ch << LCMP << IfEq(thenn) << Goto(elze)

        case _ =>
          ch << InvokeVirtual(ObjectClass, "equals", s"(L$ObjectClass;)Z")
          ch << IfEq(elze) << Goto(thenn)
      }

    case LessThan(l,r)      => mkCmpJump(cond, thenn, elze, l, r, ch, If_ICmpLt, IfLt, "lessThan")
    case GreaterThan(l,r)   => mkCmpJump(cond, thenn, elze, l, r, ch, If_ICmpGt, IfGt, "greaterThan")
    case LessEquals(l,r)    => mkCmpJump(cond, thenn, elze, l, r, ch, If_ICmpLe, IfLe, "lessEquals")
    case GreaterEquals(l,r) => mkCmpJump(cond, thenn, elze, l, r, ch, If_ICmpGe, IfGe, "greaterEquals")

    case IfExpr(c, t, e) =>
      val innerThen = ch.getFreshLabel("then")
      val innerElse = ch.getFreshLabel("else")
      mkBranch(c, innerThen, innerElse, ch)
      ch << Label(innerThen)
      mkBranch(t, thenn, elze, ch)
      ch << Label(innerElse)
      mkBranch(e, thenn, elze, ch)

    case cci @ IsConstructor(adt, id) =>
      mkExpr(cci, ch)
      ch << IfEq(elze) << Goto(thenn)

    case other if canDelegateToMkExpr =>
      mkExpr(other, ch, canDelegateToMkBranch = false)
      ch << IfEq(elze) << Goto(thenn)

    case Annotated(condition, _) =>
      mkBranch(condition, thenn, elze, ch)

    case other => throw CompilationException("Unsupported branching expr. : " + other)
  }

  /**
   *  Create a BitVector from the value on the top of the stack.
   *
   *  [[param]] is expected to be either "B", "S", "I" or "J".
   *
   *  Stack before: (..., value)
   *  Stack after:  (..., bv)
   */
  private def mkNewBV(ch: CodeHandler, param: String, size: Int): Unit = {
    ch << Comment(s"New BitVector for $param of size $size")
    ch << New(BitVectorClass)
    if (param == "J") ch << DUP_X2 << DUP_X2 << POP
    else ch << DUP_X1 << SWAP
    ch << Ldc(size)
    ch << Comment(s"Init BitVector: (${param}I)V")
    ch << InvokeSpecial(BitVectorClass, constructorName, s"(${param}I)V")
  }

  /**
   *  Generate ByteCode for BV widening and narrowing on arbitrary BV.
   *
   *  [[from]] and [[to]] are expected to be different, and at least one of
   *  them need to be a BVType(s,n) where n not in { 8, 16, 32, 64 }.
   *
   *  Stack before: (..., value)
   *  Stack after:  (..., newValue)
   *  where `value` and `newValue` are either Byte, Short, Int, Long or Reference to a BitVector
   */
  private def mkBVCast(from: Type, to: Type, ch: CodeHandler): Unit = {
    // Here, we might need to first create a BitVector.
    // We might also have to convert the resulting BitVector back to a regular integer type.
    from match {
      case Int8Type()  => mkNewBV(ch, "B", 8)
      case Int16Type() => mkNewBV(ch, "S", 16)
      case Int32Type() => mkNewBV(ch, "I", 32)
      case Int64Type() => mkNewBV(ch, "J", 64)
      case BVType(_, s) => ch << NOP
    }

    val BVType(_, oldSize) = from
    val BVType(_, newSize) = to
    ch << Comment(s"Applying BVCast on BitVector instance: $oldSize -> $newSize")
    ch << Ldc(newSize)
    ch << InvokeVirtual(BitVectorClass, "cast", s"(I)L$BitVectorClass;")

    to match {
      case Int8Type()  => ch << InvokeVirtual(BitVectorClass, "toByte", "()B")
      case Int16Type() => ch << InvokeVirtual(BitVectorClass, "toShort", "()S")
      case Int32Type() => ch << InvokeVirtual(BitVectorClass, "toInt", "()I")
      case Int64Type() => ch << InvokeVirtual(BitVectorClass, "toLong", "()J")
      case BVType(_, s) => ch << NOP
    }
  }

  private def mkBVShift(l: Expr, r: Expr, ch: CodeHandler,
                        iop: ByteCode, lop: ByteCode, op: String)
                       (using locals: Locals): Unit = {
    // NOTE for shift operations on Byte/Short/Int/Long:
    //      the lhs operand can be either Int or Long,
    //      the rhs operand must be an Int.

    def pre(ch: CodeHandler): Unit = r.getType match {
      case Int64Type() => ch << L2I
      case _ => // No need to convert the rhs argument, it is
                // either already an int, or some unrelated BVType.
    }

    def opGen(opcode: ByteCode): AbstractByteCodeGenerator = { ch =>
      pre(ch)
      ch << opcode
    }

    mkArithmeticBinaryImpl(l, r, ch, opGen(iop), opGen(lop), op, bvOnly = true)
  }

  private def mkCmpJump(cond: Expr, thenn: String, elze: String, l: Expr, r: Expr, ch: CodeHandler,
                        iop: String => ControlOperator, lop: String => ControlOperator, op: String)
                       (using locals: Locals): Unit = {
    mkExpr(l, ch)
    mkExpr(r, ch)
    l.getType match {
      case Int8Type() | Int16Type() | Int32Type() | CharType() =>
        // Here we assume the user really wants to use BitVector even for Int8/16Types.
        // Fortunately, for comparison operations, using regular Int32Type will do fine
        // as Int8/16Type are represented as Int32Type on the JVM anyway.
        ch << iop(thenn) << Goto(elze)
      case Int64Type() =>
        ch << LCMP << lop(thenn) << Goto(elze)
      case BVType(_, _) =>
        ch << InvokeVirtual(BitVectorClass, op, s"(L$BitVectorClass;)Z")
        ch << IfEq(elze) << Goto(thenn)
      case IntegerType() =>
        ch << InvokeVirtual(BigIntClass, op, s"(L$BigIntClass;)Z")
        ch << IfEq(elze) << Goto(thenn)
      case RealType() =>
        ch << InvokeVirtual(RationalClass, op, s"(L$RationalClass;)Z")
        ch << IfEq(elze) << Goto(thenn)
    }
  }

  private def mkArithmeticBinary(l: Expr, r: Expr, ch: CodeHandler,
                                 iop: ByteCode, lop: ByteCode, op: String, bvOnly: Boolean)
                                (using locals: Locals): Unit = {
    mkArithmeticBinaryImpl(l, r, ch, { ch => ch << iop }, { ch => ch << lop }, op, bvOnly)
  }

  private def mkArithmeticBinaryImpl(l: Expr, r: Expr, ch: CodeHandler,
                                     iopGen: AbstractByteCodeGenerator, lopGen: AbstractByteCodeGenerator, op: String, bvOnly: Boolean)
                                    (using locals: Locals): Unit = {
    ch << Comment(s"mkArithmeticBinary($op)")
    mkExpr(l, ch)
    mkExpr(r, ch)

    l.getType match {
      case IntegerType() if !bvOnly =>
        val opSign = s"(L$BigIntClass;)L$BigIntClass;"
        ch << Comment(s"[binary, bigint] Calling $op: $opSign")
        ch << InvokeVirtual(BigIntClass, op, opSign)

      case t @ (Int8Type() | Int16Type()) =>
        // Here we assume the user really wants to use BitVector even for Int8/16Types.
        // We therefore create two BitVector for the operation, then extract the result
        // back to the proper primitive type.

        val (param, extract, size) = t match {
          case Int8Type()  => ("B", "toByte", 8)
          case Int16Type() => ("S", "toShort", 16)
          case _ => sys.error("Unreachable") // To silence false positive warning
        }

        // stack: (l, r)
        mkNewBV(ch, param, size)
        // stack: (l, bvr)
        ch << SWAP
        mkNewBV(ch, param, size)
        ch << SWAP
        // stack: (bvl, bvr)
        val signOp = s"(L$BitVectorClass;)L$BitVectorClass;"
        ch << Comment(s"[binary, BVType(true, $size)] invoke $op on BitVector: $signOp")
        ch << InvokeVirtual(BitVectorClass, op, signOp)
        // stack: (bv)
        val signExtract = s"()$param"
        ch << Comment(s"[binary, BVType(true, $size)] invoke $extract on BitVector: $signExtract")
        ch << InvokeVirtual(BitVectorClass, extract, signExtract)

      case Int32Type() =>
        iopGen(ch)

      case Int64Type() =>
        lopGen(ch)

      case BVType(_, _) =>
        val opSign = s"(L$BitVectorClass;)L$BitVectorClass;"
        ch << Comment(s"[binary, bitvector] Calling $op: $opSign")
        ch << InvokeVirtual(BitVectorClass, op, opSign)

      case RealType() if !bvOnly =>
        val opSign = s"(L$RationalClass;)L$RationalClass;"
        ch << Comment(s"[binary, real] Calling $op: $opSign")
        ch << InvokeVirtual(RationalClass, op, opSign)
    }
  }

  private def mkArithmeticUnary(e: Expr, ch: CodeHandler,
                                iop: ByteCode, lop: ByteCode, op: String, bvOnly: Boolean)
                               (using locals: Locals): Unit = {
    mkArithmeticUnaryImpl(e, ch, { ch => ch << iop }, { ch => ch << lop }, op, bvOnly)
  }

  private def mkArithmeticUnaryImpl(e: Expr, ch: CodeHandler,
                                    iopGen: AbstractByteCodeGenerator, lopGen: AbstractByteCodeGenerator, op: String, bvOnly: Boolean)
                                   (using locals: Locals): Unit = {
    ch << Comment(s"mkArithmeticUnary($op)")
    mkExpr(e, ch)

    e.getType match {
      case IntegerType() if !bvOnly =>
        val opSign = s"()L$BigIntClass;"
        ch << Comment(s"[unary, bigint] Calling $op: $opSign")
        ch << InvokeVirtual(BigIntClass, op, opSign)

      case t @ (Int8Type() | Int16Type()) =>
        // Here we assume the user really wants to use BitVector even for Int8/16Types.
        // We therefore create a BitVector for the operation, then extract the result
        // back to the proper primitive type.

        val (param, extract, size) = t match {
          case Int8Type()  => ("B", "toByte", 8)
          case Int16Type() => ("S", "toShort", 16)
          case _ => sys.error("Unreachable") // To silence false positive warning
        }

        mkNewBV(ch, param, size)
        val signOp = s"()L$BitVectorClass;"
        ch << Comment(s"[unary, BVType(true, $size)] invoke $op on BitVector: $signOp")
        ch << InvokeVirtual(BitVectorClass, op, signOp)
        val signExtract = s"()$param"
        ch << Comment(s"[unary, BVType(true, $size)] invoke $extract on BitVector: $signExtract")
        ch << InvokeVirtual(BitVectorClass, extract, signExtract)

      case Int32Type() =>
        iopGen(ch)

      case Int64Type() =>
        lopGen(ch)

      case BVType(_, _) =>
        val opSign = s"()L$BitVectorClass;"
        ch << Comment(s"[unary, bitvector] Calling $op: $opSign")
        ch << InvokeVirtual(BitVectorClass, op, opSign)

      case RealType() if !bvOnly =>
        val opSign = s"()L$RationalClass;"
        ch << Comment(s"[unary, real] Calling $op: $opSign")
        ch << InvokeVirtual(RationalClass, op, opSign)
    }
  }


  private def load(v: Variable, ch: CodeHandler)(using locals: Locals): Unit = loadImpl(v.id, ch, Some(v.getType))

  private def loadImpl(id: Identifier, ch: CodeHandler, tpe: Option[Type] = None)(using locals: Locals): Unit = {
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
              case Some(JvmIType()) => ILoad(slot)
              case Some(Int64Type()) => LLoad(slot)
              case _ => ALoad(slot)
            })
          case None => throw CompilationException("Unknown variable : " + id)
        }
      }
    }
  }

  def compileADTSort(sort: ADTSort): Unit = {
    val cName = defSortToJVMName(sort)
    val cf = getClassSort(sort)

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
        constrParams.map(_._1).zipWithIndex.toMap.view.mapValues(_ + 1).toMap
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

  def instrumentedGetField(ch: CodeHandler, cons: TypedADTConstructor, id: Identifier)
                          (using locals: Locals): Unit = {
    cons.definition.fields.zipWithIndex.find(_._1.id == id) match {
      case Some((f, i)) =>
        val expType = cons.fields(i).getType

        val cName = defConsToJVMName(cons.definition)
        if (doInstrument) {
          ch << DUP << DUP
          ch << GetField(cName, instrumentedField, "I")
          ch << Ldc(1)
          ch << Ldc(i)
          ch << ISHL
          ch << IOR
          ch << PutField(cName, instrumentedField, "I")
        }
        ch << GetField(cName, f.id.name, typeToJVM(f.getType))

        f.getType match {
          case _: TypeParameter =>
            mkUnbox(expType, ch)
          case _ =>
        }
      case None =>
        throw CompilationException("Unknown field: "+cons.id.name+"."+id)
    }
  }

  def compileADTConstructor(cons: ADTConstructor): Unit = {
    val cName = defConsToJVMName(cons)
    val pName = defSortToJVMName(cons.getSort)
    val tcons = cons.typed

    val cf = getClassCons(cons)

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    // Case class parameters
    val fieldsTypes = cons.fields.map(vd => (vd.id, typeToJVM(vd.getType)))
    val tpeParam = if (cons.getSort.tparams.isEmpty) Seq() else Seq(tpsID -> "[I")
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
          case "B" | "S" | "I" | "Z" => ILoad(c)
          case "J" => LLoad(c)
          case _ => ALoad(c)
        })

        cch << PutField(cName, id.name, jvmt)
        c += 1
      }

      // Call parent constructor AFTER initializing case class parameters
      cch << ALoad(0)
      cch << ALoad(1)
      cch << InvokeSpecial(pName, constructorName, s"(L$MonitorClass;)V")

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
      val pnm = cf.addMethod(s"L$JavaStringClass;", "productName")
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
        instrumentedGetField(pech, tcons, f.id)(using newLocs)
        mkBox(f.getType, pech)
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
      val castSlot = ech.getFreshVar(1) // One byte for references

      // If references are equal, trees are equal.
      ech << ALoad(0) << ALoad(1) << If_ACmpNe(notRefEq) << Ldc(1) << IRETURN << Label(notRefEq)

      // We check the type (this also checks against null)....
      ech << ALoad(1) << InstanceOf(cName) << IfEq(notEq)

      // ...finally, we compare fields one by one, shortcircuiting on disequalities.
      if (cons.fields.nonEmpty) {
        ech << ALoad(1) << CheckCast(cName) << AStore(castSlot)

        for (vd <- cons.fields) {
          ech << ALoad(0)
          instrumentedGetField(ech, tcons, vd.id)(using newLocs)
          mkArrayBox(vd.getType, ech)

          ech << ALoad(castSlot)
          instrumentedGetField(ech, tcons, vd.id)(using newLocs)

          vd.getType match {
            case JvmIType() =>
              ech << If_ICmpNe(notEq)

            case Int64Type() => ???

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
      val hashFieldName = "$stainless$hashCode"
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
      hch << ALoad(0) << InvokeVirtual(cName, "productName", s"()L$JavaStringClass;")
      hch << InvokeVirtual(JavaStringClass, "hashCode", "()I")
      hch << ALoad(0) << InvokeVirtual(cName, "productElements", s"()[L$ObjectClass;")
      hch << InvokeStatic(HashingClass, "hashCode", s"([L$ObjectClass;)I") << IADD << DUP
      hch << ALoad(0) << SWAP << PutField(cName, hashFieldName, "I")
      hch << IRETURN

      hch.freeze
    }

  }

  private def internalErrorWithByteOrShort(e: Expr) =
    throw CompilationException(s"Unexpected expression involving Byte or Short: $e")
}
