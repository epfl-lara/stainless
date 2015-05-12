/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps.{simplestValue, matchToIfThenElse, collect}
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Quantification._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Defaults.constructorName
import cafebabe.Flags._

trait CodeGeneration {
  self: CompilationUnit =>

  /** A class providing information about the status of parameters in the function that is being currently compiled.
   *  vars is a mapping from local variables/ parameters to the offset of the respective JVM local register
   *  isStatic signifies if the current method is static (a function, in Leon terms)
   */
  class Locals private[codegen] (
    vars   : Map[Identifier, Int],
    args   : Map[Identifier, Int],
    fields : Map[Identifier, (String,String,String)]
  ) {
    /** Fetches the offset of a local variable/ parameter from its identifier */
    def varToLocal(v: Identifier): Option[Int] = vars.get(v)

    def varToArg(v: Identifier): Option[Int] = args.get(v)

    def varToField(v: Identifier): Option[(String,String,String)] = fields.get(v)

    /** Adds some extra variables to the mapping */
    def withVars(newVars: Map[Identifier, Int]) = new Locals(vars ++ newVars, args, fields)

    /** Adds an extra variable to the mapping */
    def withVar(nv: (Identifier, Int)) = new Locals(vars + nv, args, fields)

    def withArgs(newArgs: Map[Identifier, Int]) = new Locals(vars, args ++ newArgs, fields)

    def withFields(newFields: Map[Identifier,(String,String,String)]) = new Locals(vars, args, fields ++ newFields)
  }

  object NoLocals extends Locals(Map.empty, Map.empty, Map.empty)

  lazy val monitorID = FreshIdentifier("__$monitor")

  private[codegen] val ObjectClass               = "java/lang/Object"
  private[codegen] val BoxedIntClass             = "java/lang/Integer"
  private[codegen] val BoxedBoolClass            = "java/lang/Boolean"
  private[codegen] val BoxedCharClass            = "java/lang/Character"
  private[codegen] val BoxedArrayClass           = "leon/codegen/runtime/ArrayBox"

  private[codegen] val JavaListClass             = "java/util/List"
  private[codegen] val JavaIteratorClass         = "java/util/Iterator"

  private[codegen] val TupleClass                = "leon/codegen/runtime/Tuple"
  private[codegen] val SetClass                  = "leon/codegen/runtime/Set"
  private[codegen] val MapClass                  = "leon/codegen/runtime/Map"
  private[codegen] val BigIntClass               = "leon/codegen/runtime/BigInt"
  private[codegen] val RealClass                 = "leon/codegen/runtime/Real"
  private[codegen] val RationalClass             = "leon/codegen/runtime/Rational"
  private[codegen] val CaseClassClass            = "leon/codegen/runtime/CaseClass"
  private[codegen] val LambdaClass               = "leon/codegen/runtime/Lambda"
  private[codegen] val ErrorClass                = "leon/codegen/runtime/LeonCodeGenRuntimeException"
  private[codegen] val ImpossibleEvaluationClass = "leon/codegen/runtime/LeonCodeGenEvaluationException"
  private[codegen] val HashingClass              = "leon/codegen/runtime/LeonCodeGenRuntimeHashing"
  private[codegen] val ChooseEntryPointClass     = "leon/codegen/runtime/ChooseEntryPoint"
  private[codegen] val GenericValuesClass        = "leon/codegen/runtime/GenericValues"
  private[codegen] val MonitorClass              = "leon/codegen/runtime/LeonCodeGenRuntimeMonitor"
  private[codegen] val HenkinClass               = "leon/codegen/runtime/LeonCodeGenRuntimeHenkinMonitor"

  def idToSafeJVMName(id: Identifier) = {
    scala.reflect.NameTransformer.encode(id.uniqueName).replaceAll("\\.", "\\$")
  }
  def defToJVMName(d : Definition) : String = "Leon$CodeGen$" + idToSafeJVMName(d.id)

  /** Retrieve the name of the underlying lazy field from a lazy field accessor method */
  private[codegen] def underlyingField(lazyAccessor : String) = lazyAccessor + "$underlying"

  protected object ValueType {
    def unapply(tp: TypeTree): Boolean = tp match {
      case Int32Type | BooleanType | CharType | UnitType => true
      case _ => false
    }
  }

  /** Return the respective JVM type from a Leon type */
  def typeToJVM(tpe : TypeTree) : String = tpe match {
    case Int32Type => "I"

    case BooleanType => "Z"

    case CharType => "C"

    case UnitType => "Z"

    case c : ClassType =>
      leonClassToJVMInfo(c.classDef).map { case (n, _) => "L" + n + ";" }.getOrElse(
        throw CompilationException("Unsupported class " + c.id)
      )

    case _ : TupleType =>
      "L" + TupleClass + ";"

    case _ : SetType =>
      "L" + SetClass + ";"

    case _ : MapType =>
      "L" + MapClass + ";"

    case IntegerType =>
      "L" + BigIntClass + ";"

    case RealType =>
      "L" + RationalClass + ";"

    case _ : FunctionType =>
      "L" + LambdaClass + ";"

    case ArrayType(base) =>
      "[" + typeToJVM(base)

    case TypeParameter(_) =>
      "L" + ObjectClass + ";"

    case _ => throw CompilationException("Unsupported type : " + tpe)
  }

  /** Return the respective boxed JVM type from a Leon type */
  def typeToJVMBoxed(tpe : TypeTree) : String = tpe match {
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
  def compileFunDef(funDef: FunDef, owner: Definition) {
    val isStatic = owner.isInstanceOf[ModuleDef]

    val cf = classes(owner)
    val (_,mn,_) = leonFunDefToJVMInfo(funDef).get

    val paramsTypes = funDef.params.map(a => typeToJVM(a.getType))

    val realParams = if (requireMonitor) {
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
      // FIXME Not sure about this "FINAL" now that we can have methods in inheritable classes
      if (isStatic)
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL  |
        METHOD_ACC_STATIC
      else
        METHOD_ACC_PUBLIC |
        METHOD_ACC_FINAL
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    // An offset we introduce to the parameters:
    // 1 if this is a method, so we need "this" in position 0 of the stack
    // 1 if we are monitoring
    val idParams = (if (requireMonitor) Seq(monitorID) else Seq.empty) ++ funDef.params.map(_.id)
    val newMapping = idParams.zipWithIndex.toMap.mapValues(_ + (if (!isStatic) 1 else 0))

    val body = funDef.body.getOrElse(throw CompilationException("Can't compile a FunDef without body: "+funDef.id.name))

    val bodyWithPre = if(funDef.hasPrecondition && params.checkContracts) {
      IfExpr(funDef.precondition.get, body, Error(body.getType, "Precondition failed"))
    } else {
      body
    }

    val bodyWithPost = funDef.postcondition match {
      case Some(post) if params.checkContracts =>
        Ensuring(bodyWithPre, post).toAssert
      case _ => bodyWithPre
    }

    val locals = NoLocals.withVars(newMapping)

    if (params.recordInvocations) {
      load(monitorID, ch)(locals)
      ch << InvokeVirtual(MonitorClass, "onInvoke", "()V")
    }

    mkExpr(bodyWithPost, ch)(locals)

    funDef.returnType match {
      case ValueType() =>
        ch << IRETURN

      case _ =>
        ch << ARETURN
    }

    ch.freeze
  }

  private[codegen] val lambdaToClass = scala.collection.mutable.Map.empty[Lambda, String]
  private[codegen] val classToLambda = scala.collection.mutable.Map.empty[String, Lambda]

  private def compileLambda(l: Lambda, ch: CodeHandler)(implicit locals: Locals): Unit = {
    val (normalized, structSubst) = purescala.ExprOps.normalizeStructure(l)
    val reverseSubst = structSubst.map(p => p._2 -> p._1)
    val nl = normalized.asInstanceOf[Lambda]

    val closureIDs = purescala.ExprOps.variablesOf(nl).toSeq.sortBy(_.uniqueName)
    val closuresWithoutMonitor = closureIDs.map(id => id -> typeToJVM(id.getType))
    val closures = if (requireMonitor) {
      (monitorID -> s"L$MonitorClass;") +: closuresWithoutMonitor
    } else closuresWithoutMonitor

    val afName = lambdaToClass.getOrElse(nl, {
      val afName = "Leon$CodeGen$Lambda$" + lambdaCounter.nextGlobal
      lambdaToClass += nl -> afName
      classToLambda += afName -> nl

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

      locally {
        val apm = cf.addMethod(s"L$ObjectClass;", "apply", s"[L$ObjectClass;")

        apm.setFlags((
          METHOD_ACC_PUBLIC |
          METHOD_ACC_FINAL
        ).asInstanceOf[U2])

        val argMapping = nl.args.map(_.id).zipWithIndex.toMap
        val closureMapping = closures.map { case (id, jvmt) => id -> (afName, id.uniqueName, jvmt) }.toMap

        val newLocals = locals.withArgs(argMapping).withFields(closureMapping)

        val apch = apm.codeHandler

        mkBoxedExpr(nl.body, apch)(newLocals)

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
        if(closures.nonEmpty) {
          ech << ALoad(1) << CheckCast(afName) << AStore(castSlot)

          for((id,jvmt) <- closures) {
            ech << ALoad(0) << GetField(afName, id.uniqueName, jvmt)
            ech << ALoad(castSlot) << GetField(afName, id.uniqueName, jvmt)

            jvmt match {
              case "I" | "Z" =>
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
        for (((id, jvmt),i) <- closuresWithoutMonitor.zipWithIndex) {
          hch << DUP << Ldc(i)
          hch << ALoad(0) << GetField(afName, id.uniqueName, jvmt)
          mkBox(id.getType, hch)
          hch << AASTORE
        }

        hch << Ldc(afName.hashCode)
        hch << InvokeStatic(HashingClass, "seqHash", s"([L$ObjectClass;I)I") << DUP
        hch << ALoad(0) << SWAP << PutField(afName, hashFieldName, "I")
        hch << IRETURN

        hch.freeze
      }

      loader.register(cf)

      afName
    })

    val consSig = "(" + closures.map(_._2).mkString("") + ")V"

    ch << New(afName) << DUP
    for ((id,jvmt) <- closures) {
      if (id == monitorID) {
        load(monitorID, ch)
      } else {
        mkExpr(Variable(reverseSubst(id)), ch)
      }
    }
    ch << InvokeSpecial(afName, constructorName, consSig)
  }

  private val typeIdCache = scala.collection.mutable.Map.empty[TypeTree, Int]
  private[codegen] def typeId(tpe: TypeTree): Int = typeIdCache.get(tpe) match {
    case Some(id) => id
    case None =>
      val id = typeIdCache.size
      typeIdCache += tpe -> id
      id
  }

  private def compileForall(f: Forall, ch: CodeHandler)(implicit locals: Locals): Unit = {
    // make sure we have an available HenkinModel
    val monitorOk = ch.getFreshLabel("monitorOk")
    load(monitorID, ch)
    ch << InstanceOf(HenkinClass) << IfNe(monitorOk)
    ch << New(ImpossibleEvaluationClass) << DUP
    ch << Ldc("Can't evaluate foralls without domain")
    ch << InvokeSpecial(ImpossibleEvaluationClass, constructorName, "(Ljava/lang/String;)V")
    ch << ATHROW
    ch << Label(monitorOk)

    val Forall(fargs, TopLevelAnds(conjuncts)) = f
    val endLabel = ch.getFreshLabel("forallEnd")

    for (conj <- conjuncts) {
      val vars = purescala.ExprOps.variablesOf(conj)
      val args = fargs.map(_.id).filter(vars)
      val quantified = args.toSet

      val matchQuorums = extractQuorums(conj, quantified)

      val matcherIndexes = matchQuorums.flatten.distinct.zipWithIndex.toMap

      def buildLoops(
        mis: List[(Expr, Seq[Expr], Int)],
        localMapping: Map[Identifier, Int],
        pointerMapping: Map[(Int, Int), Identifier]
      ): Unit = mis match {
        case (expr, args, qidx) :: rest =>
          load(monitorID, ch)
          ch << CheckCast(HenkinClass)

          mkExpr(expr, ch)
          ch << Ldc(typeId(expr.getType))
          ch << InvokeVirtual(HenkinClass, "domain", s"(L$ObjectClass;I)L$JavaListClass;")
          ch << InvokeInterface(JavaListClass, "iterator", s"()L$JavaIteratorClass;")

          val loop = ch.getFreshLabel("loop")
          val out = ch.getFreshLabel("out")
          ch << Label(loop)
          // it
          ch << DUP
          // it, it
          ch << InvokeInterface(JavaIteratorClass, "hasNext", "()Z")
          // it, hasNext
          ch << IfEq(out) << DUP
          // it, it
          ch << InvokeInterface(JavaIteratorClass, "next", s"()L$ObjectClass;")
          // it, elem
          ch << CheckCast(TupleClass)

          val (newLoc, newPtr) = (for ((arg, aidx) <- args.zipWithIndex) yield {
            val id = FreshIdentifier("q", arg.getType, true)
            val slot = ch.getFreshVar

            ch << DUP << Ldc(aidx) << InvokeVirtual(TupleClass, "get", s"(I)L$ObjectClass;")
            mkUnbox(arg.getType, ch)
            ch << (typeToJVM(arg.getType) match {
              case "I" | "Z" => IStore(slot)
              case _ => AStore(slot)
            })

            (id -> slot, (qidx -> aidx) -> id)
          }).unzip

          ch << POP
          // it

          buildLoops(rest, localMapping ++ newLoc, pointerMapping ++ newPtr)

          ch << Goto(loop)
          ch << Label(out) << POP

        case Nil =>
          var okLabel: Option[String] = None
          for (quorum <- matchQuorums) {
            okLabel.foreach(ok => ch << Label(ok))
            okLabel = Some(ch.getFreshLabel("quorumOk"))

            var mappings: Seq[(Identifier, Int, Int)] = Seq.empty
            var constraints: Seq[(Expr, Int, Int)] = Seq.empty
            var equalities: Seq[((Int, Int), (Int, Int))] = Seq.empty

            for (q @ (expr, args) <- quorum) {
              val qidx = matcherIndexes(q)
              val (qmappings, qconstraints) = args.zipWithIndex.partition {
                case (Variable(id), aidx) => quantified(id)
                case _ => false
              }

              mappings ++= qmappings.map(p => (p._1.asInstanceOf[Variable].id, qidx, p._2))
              constraints ++= qconstraints.map(p => (p._1, qidx, p._2))
            }

            val mapping = for ((id, es) <- mappings.groupBy(_._1)) yield {
              val base :: others = es.toList.map(p => (p._2, p._3))
              equalities ++= others.map(p => base -> p)
              (id -> base)
            }

            val enabler = andJoin(constraints.map {
              case (e, qidx, aidx) => Equals(e, pointerMapping(qidx -> aidx).toVariable)
            } ++ equalities.map {
              case (k1, k2) => Equals(pointerMapping(k1).toVariable, pointerMapping(k2).toVariable)
            })

            mkExpr(enabler, ch)(locals.withVars(localMapping))
            ch << IfEq(okLabel.get)

            val varsMap = args.map(id => id -> localMapping(pointerMapping(mapping(id)))).toMap
            mkExpr(conj, ch)(locals.withVars(varsMap))
            ch << IfNe(okLabel.get)

            // -- Forall is false! --
            // POP all the iterators...
            for (_ <- List.range(0, matcherIndexes.size)) ch << POP

            // ... and return false
            ch << Ldc(0) << Goto(endLabel)
          }

          ch << Label(okLabel.get)
      }

      buildLoops(matcherIndexes.toList.map { case ((e, as), idx) => (e, as, idx) }, Map.empty, Map.empty)
    }

    ch << Ldc(1) << Label(endLabel)
  }

  private[codegen] def mkExpr(e: Expr, ch: CodeHandler, canDelegateToMkBranch: Boolean = true)(implicit locals: Locals) {
    e match {
      case Variable(id) =>
        load(id, ch)

      case Assert(cond, oerr, body) =>
        mkExpr(IfExpr(Not(cond), Error(body.getType, oerr.getOrElse("Assertion failed @"+e.getPos)), body), ch)

      case en @ Ensuring(_, _) =>
        mkExpr(en.toAssert, ch)

      case Let(i,d,b) =>
        mkExpr(d, ch)
        val slot = ch.getFreshVar
        val instr = i.getType match {
          case ValueType() => IStore(slot)
          case _ => AStore(slot)
        }
        ch << instr
        mkExpr(b, ch)(locals.withVar(i -> slot))

      case IntLiteral(v) =>
        ch << Ldc(v)

      case CharLiteral(v) =>
        ch << Ldc(v)

      case BooleanLiteral(v) =>
        ch << Ldc(if(v) 1 else 0)

      case UnitLiteral() =>
        ch << Ldc(1)

      case InfiniteIntegerLiteral(v) =>
        ch << New(BigIntClass) << DUP
        ch << Ldc(v.toString)
        ch << InvokeSpecial(BigIntClass, constructorName, "(Ljava/lang/String;)V")

      case FractionalLiteral(n, d) =>
        ch << New(RationalClass) << DUP
        ch << Ldc(n.toString)
        ch << Ldc(d.toString)
        ch << InvokeSpecial(RationalClass, constructorName, "(Ljava/lang/String;Ljava/lang/String;)V")

      // Case classes
      case CaseClass(cct, as) =>
        val (ccName, ccApplySig) = leonClassToJVMInfo(cct.classDef).getOrElse {
          throw CompilationException("Unknown class : " + cct.id)
        }
        ch << New(ccName) << DUP
        if (requireMonitor) {
          load(monitorID, ch)
        }

        for((a, vd) <- as zip cct.classDef.fields) {
          vd.getType match {
            case TypeParameter(_) =>
              mkBoxedExpr(a, ch)
            case _ =>
              mkExpr(a, ch)
          }
        }
        ch << InvokeSpecial(ccName, constructorName, ccApplySig)

      case IsInstanceOf(e, cct) =>
        val (ccName, _) = leonClassToJVMInfo(cct.classDef).getOrElse {
          throw CompilationException("Unknown class : " + cct.id)
        }
        mkExpr(e, ch)
        ch << InstanceOf(ccName)

      case AsInstanceOf(e, cct) =>
        val (ccName, _) = leonClassToJVMInfo(cct.classDef).getOrElse {
          throw CompilationException("Unknown class : " + cct.id)
        }
        mkExpr(e, ch)
        ch << CheckCast(ccName)

      case CaseClassSelector(cct, e, sid) =>
        mkExpr(e, ch)
        val (ccName, _) = leonClassToJVMInfo(cct.classDef).getOrElse {
          throw CompilationException("Unknown class : " + cct.id)
        }
        ch << CheckCast(ccName)
        instrumentedGetField(ch, cct, sid)

      // Tuples (note that instanceOf checks are in mkBranch)
      case Tuple(es) =>
        ch << New(TupleClass) << DUP
        ch << Ldc(es.size)
        ch << NewArray(s"$ObjectClass")
        for((e,i) <- es.zipWithIndex) {
          ch << DUP
          ch << Ldc(i)
          mkBoxedExpr(e, ch)
          ch << AASTORE
        }
        ch << InvokeSpecial(TupleClass, constructorName, s"([L$ObjectClass;)V")

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
          ch << InvokeVirtual(SetClass, "add", s"(L$ObjectClass;)V")
        }

      case ElementOfSet(e, s) =>
        mkExpr(s, ch)
        mkBoxedExpr(e, ch)
        ch << InvokeVirtual(SetClass, "contains", s"(L$ObjectClass;)Z")

      case SetCardinality(s) =>
        mkExpr(s, ch)
        ch << InvokeVirtual(SetClass, "size", "()I")

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
        ch << InvokeVirtual(SetClass, "minus", s"(L$SetClass;)L$SetClass;")

      // Maps
      case FiniteMap(ss, _, _) =>
        ch << DefaultNew(MapClass)
        for((f,t) <- ss) {
          ch << DUP
          mkBoxedExpr(f, ch)
          mkBoxedExpr(t, ch)
          ch << InvokeVirtual(MapClass, "add", s"(L$ObjectClass;L$ObjectClass;)V")
        }

      case MapApply(m, k) =>
        val MapType(_, tt) = m.getType
        mkExpr(m, ch)
        mkBoxedExpr(k, ch)
        ch << InvokeVirtual(MapClass, "get", s"(L$ObjectClass;)L$ObjectClass;")
        mkUnbox(tt, ch)

      case MapIsDefinedAt(m, k) =>
        mkExpr(m, ch)
        mkBoxedExpr(k, ch)
        ch << InvokeVirtual(MapClass, "isDefinedAt", s"(L$ObjectClass;)Z")

      case MapUnion(m1, m2) =>
        mkExpr(m1, ch)
        mkExpr(m2, ch)
        ch << InvokeVirtual(MapClass, "union", s"(L$MapClass;)L$MapClass;")

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

      // Strict static fields
      case FunctionInvocation(tfd, as) if tfd.fd.canBeStrictField =>
        val (className, fieldName, _) = leonFunDefToJVMInfo(tfd.fd).getOrElse {
          throw CompilationException("Unknown method : " + tfd.id)
        }

        if (requireMonitor) {
          load(monitorID, ch)
          ch << InvokeVirtual(MonitorClass, "onInvoke", "()V")
        }

        // Get static field
        ch << GetStatic(className, fieldName, typeToJVM(tfd.fd.returnType))

        // unbox field
        (tfd.fd.returnType, tfd.returnType) match {
          case (TypeParameter(_), tpe)  =>
            mkUnbox(tpe, ch)
          case _ =>
        }

      case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq(set)) if fd == program.library.setToList.get =>

        val nil = CaseClass(CaseClassType(program.library.Nil.get, Seq(tp)), Seq())
        val cons = program.library.Cons.get
        val (consName, ccApplySig) = leonClassToJVMInfo(cons).getOrElse {
          throw CompilationException("Unknown class : " + cons)
        }

        mkExpr(nil, ch)
        mkExpr(set, ch)
        //if (params.requireMonitor) {
        //  ch << ALoad(locals.monitorIndex)
        //}

        // No dynamic dispatching/overriding in Leon,
        // so no need to take care of own vs. "super" methods
        ch << InvokeVirtual(SetClass, "getElements", s"()L$JavaIteratorClass;")

        val loop = ch.getFreshLabel("loop")
        val out = ch.getFreshLabel("out")
        ch << Label(loop)
        // list, it
        ch << DUP
        // list, it, it
        ch << InvokeInterface(JavaIteratorClass, "hasNext", "()Z")
        // list, it, hasNext
        ch << IfEq(out)
        // list, it
        ch << DUP2
        // list, it, list, it
        ch << InvokeInterface(JavaIteratorClass, "next", s"()L$ObjectClass;") << SWAP
        // list, it, elem, list
        ch << New(consName) << DUP << DUP2_X2
        // list, it, cons, cons, elem, list, cons, cons
        ch << POP << POP
        // list, it, cons, cons, elem, list

        if (requireMonitor) {
          load(monitorID, ch)
          ch << DUP_X2 << POP
        }
        ch << InvokeSpecial(consName, constructorName, ccApplySig)
        // list, it, newList
        ch << DUP_X2 << POP << SWAP << POP
        // newList, it
        ch << Goto(loop)

        ch << Label(out)
        // list, it
        ch << POP
        // list

      // Static lazy fields/ functions
      case fi @ FunctionInvocation(tfd, as) =>
        val (cn, mn, ms) = leonFunDefToJVMInfo(tfd.fd).getOrElse {
          throw CompilationException("Unknown method : " + tfd.id)
        }

        if (requireMonitor) {
          load(monitorID, ch)
        }

        for((a, vd) <- as zip tfd.fd.params) {
          vd.getType match {
            case TypeParameter(_) =>
              mkBoxedExpr(a, ch)
            case _ =>
              mkExpr(a, ch)
          }
        }

        ch << InvokeStatic(cn, mn, ms)

        (tfd.fd.returnType, tfd.returnType) match {
          case (TypeParameter(_), tpe)  =>
            mkUnbox(tpe, ch)
          case _ =>
        }

      // Strict fields are handled as fields
      case MethodInvocation(rec, _, tfd, _) if tfd.fd.canBeStrictField =>
        val (className, fieldName, _) = leonFunDefToJVMInfo(tfd.fd).getOrElse {
          throw CompilationException("Unknown method : " + tfd.id)
        }

        if (requireMonitor) {
          load(monitorID, ch)
          ch << InvokeVirtual(MonitorClass, "onInvoke", "()V")
        }
        // Load receiver
        mkExpr(rec,ch)

        // Get field
        ch << GetField(className, fieldName, typeToJVM(tfd.fd.returnType))

        // unbox field
        (tfd.fd.returnType, tfd.returnType) match {
          case (TypeParameter(_), tpe)  =>
            mkUnbox(tpe, ch)
          case _ =>
        }

      // This is for lazy fields and real methods.
      // To access a lazy field, we call its accessor function.
      case MethodInvocation(rec, cd, tfd, as) =>
        val (className, methodName, sig) = leonFunDefToJVMInfo(tfd.fd).getOrElse {
          throw CompilationException("Unknown method : " + tfd.id)
        }

        // Receiver of the method call
        mkExpr(rec,ch)

        if (requireMonitor) {
          load(monitorID, ch)
        }

        for((a, vd) <- as zip tfd.fd.params) {
          vd.getType match {
            case TypeParameter(_) =>
              mkBoxedExpr(a, ch)
            case _ =>
              mkExpr(a, ch)
          }
        }

        // No interfaces in Leon, so no need to use InvokeInterface
        ch << InvokeVirtual(className, methodName, sig)

        (tfd.fd.returnType, tfd.returnType) match {
          case (TypeParameter(_), tpe)  =>
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

      case l @ Lambda(args, body) =>
        compileLambda(l, ch)

      case f @ Forall(args, body) =>
        compileForall(f, ch)

      // Arithmetic
      case Plus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "add", s"(L$BigIntClass;)L$BigIntClass;")

      case Minus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "sub", s"(L$BigIntClass;)L$BigIntClass;")

      case Times(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "mult", s"(L$BigIntClass;)L$BigIntClass;")

      case Division(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "div", s"(L$BigIntClass;)L$BigIntClass;")

      case Remainder(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "rem", s"(L$BigIntClass;)L$BigIntClass;")

      case Modulo(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(BigIntClass, "mod", s"(L$BigIntClass;)L$BigIntClass;")

      case UMinus(e) =>
        mkExpr(e, ch)
        ch << InvokeVirtual(BigIntClass, "neg", s"()L$BigIntClass;")

      case RealPlus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(RationalClass, "add", s"(L$RationalClass;)L$RationalClass;")

      case RealMinus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(RationalClass, "sub", s"(L$RationalClass;)L$RationalClass;")

      case RealTimes(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(RationalClass, "mult", s"(L$RationalClass;)L$RationalClass;")

      case RealDivision(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << InvokeVirtual(RationalClass, "div", s"(L$RationalClass;)L$RationalClass;")

      case RealUMinus(e) =>
        mkExpr(e, ch)
        ch << InvokeVirtual(RationalClass, "neg", s"()L$RationalClass;")


      //BV arithmetic
      case BVPlus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IADD

      case BVMinus(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << ISUB

      case BVTimes(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IMUL

      case BVDivision(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IDIV

      case BVRemainder(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IREM

      case BVUMinus(e) =>
        mkExpr(e, ch)
        ch << INEG

      case BVNot(e) =>
        mkExpr(e, ch)
        mkExpr(IntLiteral(-1), ch)
        ch << IXOR

      case BVAnd(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IAND

      case BVOr(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IOR

      case BVXOr(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IXOR

      case BVShiftLeft(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << ISHL

      case BVLShiftRight(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << IUSHR

      case BVAShiftRight(l, r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        ch << ISHR

      case ArrayLength(a) =>
        mkExpr(a, ch)
        ch << ARRAYLENGTH

      case as @ ArraySelect(a,i) =>
        mkExpr(a, ch)
        mkExpr(i, ch)
        ch << (as.getType match {
          case Untyped => throw CompilationException("Cannot compile untyped array access.")
          case CharType => CALOAD
          case Int32Type => IALOAD
          case BooleanType => BALOAD
          case _ => AALOAD
        })

      case au @ ArrayUpdated(a, i, v) =>
        mkExpr(a, ch)
        ch << DUP
        ch << ARRAYLENGTH
        val storeInstr = a.getType match {
          case ArrayType(CharType) => ch << NewArray.primitive("T_CHAR"); CASTORE
          case ArrayType(Int32Type) => ch << NewArray.primitive("T_INT"); IASTORE
          case ArrayType(BooleanType) => ch << NewArray.primitive("T_BOOLEAN"); BASTORE
          case ArrayType(other) => ch << NewArray(typeToJVM(other)); AASTORE
          case other => throw CompilationException(s"Cannot compile finite array expression whose type is $other.")
        }
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

      case a @ FiniteArray(elems, default, length) =>
        val IntLiteral(l) = length
        ch << Ldc(l)
        val storeInstr = a.getType match {
          case ArrayType(CharType) => ch << NewArray.primitive("T_CHAR"); CASTORE
          case ArrayType(Int32Type) => ch << NewArray.primitive("T_INT"); IASTORE
          case ArrayType(BooleanType) => ch << NewArray.primitive("T_BOOLEAN"); BASTORE
          case ArrayType(other) => ch << NewArray(typeToJVM(other)); AASTORE
          case other => throw CompilationException(s"Cannot compile finite array expression whose type is $other.")
        }

        for (i <- 0 until l) {
          val v = elems.get(i).orElse(default).getOrElse {
            throw CompilationException(s"No valuation for key '$i' in array")
          }

          ch << DUP << Ldc(i)
          mkExpr(v, ch)
          ch << storeInstr
        }

      // Misc and boolean tests
      case Error(tpe, desc) =>
        ch << New(ErrorClass) << DUP
        ch << Ldc(desc)
        ch << InvokeSpecial(ErrorClass, constructorName, "(Ljava/lang/String;)V")
        ch << ATHROW

      case choose: Choose =>
        val prob = synthesis.Problem.fromChoose(choose)

        val id = runtime.ChooseEntryPoint.register(prob, this)
        ch << Ldc(id)

        ch << Ldc(prob.as.size)
        ch << NewArray(ObjectClass)

        for ((id, i) <- prob.as.zipWithIndex) {
          ch << DUP
          ch << Ldc(i)
          mkExpr(Variable(id), ch)
          mkBox(id.getType, ch)
          ch << AASTORE
        }

        ch << InvokeStatic(ChooseEntryPointClass, "invoke", s"(I[L$ObjectClass;)L$ObjectClass;")

        mkUnbox(choose.getType, ch)

      case gv @ GenericValue(tp, int) =>
        val id = runtime.GenericValues.register(gv)
        ch << Ldc(id)
        ch << InvokeStatic(GenericValuesClass, "get", s"(I)L$ObjectClass;")

      case nt @ NoTree( tp@ValueType() ) =>
        mkExpr(simplestValue(tp), ch)

      case NoTree(_) =>
        ch << ACONST_NULL

      case This(ct) =>
        ch << ALoad(0)

      case p : Passes =>
        mkExpr(matchToIfThenElse(p.asConstraint), ch)

      case m : MatchExpr =>
        mkExpr(matchToIfThenElse(m), ch)

      case b if b.getType == BooleanType && canDelegateToMkBranch =>
        val fl = ch.getFreshLabel("boolfalse")
        val al = ch.getFreshLabel("boolafter")
        ch << Ldc(1)
        mkBranch(b, al, fl, ch, canDelegateToMkExpr = false)
        ch << Label(fl) << POP << Ldc(0) << Label(al)

      case _ => throw CompilationException("Unsupported expr " + e + " : " + e.getClass)
    }
  }

  // Leaves on the stack a value equal to `e`, always of a type compatible with java.lang.Object.
  private[codegen] def mkBoxedExpr(e: Expr, ch: CodeHandler)(implicit locals: Locals) {
    e.getType match {
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

      case at @ ArrayType(et) =>
        ch << New(BoxedArrayClass) << DUP
        mkExpr(e, ch)
        ch << InvokeSpecial(BoxedArrayClass, constructorName, s"(${typeToJVM(at)})V")

      case _ =>
        mkExpr(e, ch)
    }
  }

  // Assumes the top of the stack contains of value of the right type, and makes it
  // compatible with java.lang.Object.
  private[codegen] def mkBox(tpe: TypeTree, ch: CodeHandler)(implicit locals: Locals) {
    tpe match {
      case Int32Type =>
        ch << New(BoxedIntClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedIntClass, constructorName, "(I)V")

      case BooleanType | UnitType =>
        ch << New(BoxedBoolClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedBoolClass, constructorName, "(Z)V")

      case CharType =>
        ch << New(BoxedCharClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedCharClass, constructorName, "(C)V")

      case at @ ArrayType(et) =>
        ch << New(BoxedArrayClass) << DUP_X1 << SWAP << InvokeSpecial(BoxedArrayClass, constructorName, s"(${typeToJVM(at)})V")
      case _ =>
    }
  }

  // Assumes that the top of the stack contains a value that should be of type `tpe`, and unboxes it to the right (JVM) type.
  private[codegen] def mkUnbox(tpe: TypeTree, ch: CodeHandler)(implicit locals: Locals) {
    tpe match {
      case Int32Type =>
        ch << CheckCast(BoxedIntClass) << InvokeVirtual(BoxedIntClass, "intValue", "()I")

      case BooleanType | UnitType =>
        ch << CheckCast(BoxedBoolClass) << InvokeVirtual(BoxedBoolClass, "booleanValue", "()Z")

      case CharType =>
        ch << CheckCast(BoxedCharClass) << InvokeVirtual(BoxedCharClass, "charValue", "()C")

      case ct : ClassType =>
        val (cn, _) = leonClassToJVMInfo(ct.classDef).getOrElse {
          throw new CompilationException("Unsupported class type : " + ct)
        }
        ch << CheckCast(cn)

      case IntegerType =>
        ch << CheckCast(BigIntClass)

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

      case tp : ArrayType =>
        ch << CheckCast(BoxedArrayClass) << InvokeVirtual(BoxedArrayClass, "arrayValue", s"()${typeToJVM(tp)}")
        ch << CheckCast(typeToJVM(tp))

      case _ =>
        throw new CompilationException("Unsupported type in unboxing : " + tpe)
    }
  }

  private[codegen] def mkBranch(cond: Expr, thenn: String, elze: String, ch: CodeHandler, canDelegateToMkExpr: Boolean = true)(implicit locals: Locals) {
    cond match {
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

      case Variable(b) =>
        load(b, ch)
        ch << IfEq(elze) << Goto(thenn)

      case Equals(l,r) =>
        mkExpr(l, ch)
        mkExpr(r, ch)
        l.getType match {
          case ValueType() =>
            ch << If_ICmpEq(thenn) << Goto(elze)

          case _ =>
            ch << InvokeVirtual(s"$ObjectClass", "equals", s"(L$ObjectClass;)Z")
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

      case cci@IsInstanceOf(cct, e) =>
        mkExpr(cci, ch)
        ch << IfEq(elze) << Goto(thenn)

      case other if canDelegateToMkExpr =>
        mkExpr(other, ch, canDelegateToMkBranch = false)
        ch << IfEq(elze) << Goto(thenn)

      case other => throw CompilationException("Unsupported branching expr. : " + other)
    }
  }

  private def load(id: Identifier, ch: CodeHandler)(implicit locals: Locals): Unit = {
    locals.varToArg(id) match {
      case Some(slot) =>
        ch << ALoad(1) << Ldc(slot) << AALOAD
        mkUnbox(id.getType, ch)
      case None => locals.varToField(id) match {
        case Some((afName, nme, tpe)) =>
          ch << ALoad(0) << GetField(afName, nme, tpe)
        case None => locals.varToLocal(id) match {
          case Some(slot) =>
            val instr = id.getType match {
              case ValueType() => ILoad(slot)
              case _ => ALoad(slot)
            }
            ch << instr
          case None => throw CompilationException("Unknown variable : " + id)
        }
      }
    }
  }

  /** Compiles a lazy field.
    *
    * To define a lazy field, we have to add an accessor method and an underlying field.
    * The accessor method has the name of the original (Scala) lazy field and can be public.
    * The underlying field has a different name, is private, and is of a boxed type
    * to support null value (to signify uninitialized).
    *
    * @param lzy The lazy field to be compiled
    * @param owner The module/class containing `lzy`
    */
  def compileLazyField(lzy: FunDef, owner: Definition) {
    ctx.reporter.internalAssertion(lzy.canBeLazyField, s"Trying to compile non-lazy ${lzy.id.name} as a lazy field")

    val (_, accessorName, _ ) = leonFunDefToJVMInfo(lzy).get
    val cf = classes(owner)
    val cName = defToJVMName(owner)

    val isStatic = owner.isInstanceOf[ModuleDef]

    // Name of the underlying field
    val underlyingName = underlyingField(accessorName)
    // Underlying field is of boxed type
    val underlyingType = typeToJVMBoxed(lzy.returnType)

    // Underlying field. It is of a boxed type
    val fh = cf.addField(underlyingType,underlyingName)
    fh.setFlags( if (isStatic) {(
      FIELD_ACC_STATIC |
      FIELD_ACC_PRIVATE
    ).asInstanceOf[U2] } else {
      FIELD_ACC_PRIVATE
    }) // FIXME private etc?

    // accessor method
    locally {
      val parameters = if (requireMonitor) {
        Seq(monitorID -> s"L$MonitorClass;")
      } else Seq()

      val paramMapping = parameters.map(_._1).zipWithIndex.toMap.mapValues(_ + (if (isStatic) 0 else 1))
      val newLocs = NoLocals.withVars(paramMapping)

      val accM = cf.addMethod(typeToJVM(lzy.returnType), accessorName, parameters.map(_._2) : _*)
      accM.setFlags( if (isStatic) {(
        METHOD_ACC_STATIC | // FIXME other flags? Not always public?
        METHOD_ACC_PUBLIC
      ).asInstanceOf[U2] } else {
        METHOD_ACC_PUBLIC
      })
      val ch = accM.codeHandler
      val body = lzy.body.getOrElse(throw CompilationException("Lazy field without body?"))
      val initLabel = ch.getFreshLabel("isInitialized")

      if (requireMonitor) {
        load(monitorID, ch)(newLocs)
        ch << InvokeVirtual(MonitorClass, "onInvoke", "()V")
      }

      if (isStatic) {
        ch << GetStatic(cName, underlyingName, underlyingType)
      } else {
        ch << ALoad(0) << GetField(cName, underlyingName, underlyingType) // if (lzy == null)
      }
      // oldValue
      ch << DUP << IfNonNull(initLabel)
      // null
      ch << POP
      //
      mkBoxedExpr(body,ch)(newLocs) // lzy = <expr>
      ch << DUP
      // newValue, newValue
      if (isStatic) {
        ch << PutStatic(cName, underlyingName, underlyingType)
        //newValue
      }
      else {
        ch << ALoad(0) << SWAP
        // newValue, object, newValue
        ch << PutField (cName, underlyingName, underlyingType)
        //newValue
      }
      ch << Label(initLabel)  // return lzy
      //newValue
      lzy.returnType match {
        case ValueType() =>
          // Since the underlying field only has boxed types, we have to unbox them to return them
          mkUnbox(lzy.returnType, ch)(newLocs)
          ch << IRETURN
        case _ =>
          ch << ARETURN
      }
      ch.freeze
    }
  }

  /** Compile the (strict) field `field` which is owned by class `owner` */
  def compileStrictField(field : FunDef, owner : Definition) = {

    ctx.reporter.internalAssertion(field.canBeStrictField,
      s"Trying to compile ${field.id.name} as a strict field")
    val (_, fieldName, _) = leonFunDefToJVMInfo(field).get

    val cf = classes(owner)
    val fh = cf.addField(typeToJVM(field.returnType),fieldName)
    fh.setFlags( owner match {
      case _ : ModuleDef => (
        FIELD_ACC_STATIC |
        FIELD_ACC_PUBLIC | // FIXME
        FIELD_ACC_FINAL
      ).asInstanceOf[U2]
      case _ => (
        FIELD_ACC_PUBLIC | // FIXME
        FIELD_ACC_FINAL
      ).asInstanceOf[U2]
    })
  }

  /** Initializes a lazy field to null
   *  @param ch the codehandler to add the initializing code to
   *  @param className the name of the class in which the field is initialized
   *  @param lzy the lazy field to be initialized
   *  @param isStatic true if this is a static field
   */
  def initLazyField(ch: CodeHandler, className: String,  lzy: FunDef, isStatic: Boolean)(implicit locals: Locals) = {
    val (_, name, _) = leonFunDefToJVMInfo(lzy).get
    val underlyingName = underlyingField(name)
    val jvmType = typeToJVMBoxed(lzy.returnType)
    if (isStatic){
      ch << ACONST_NULL << PutStatic(className, underlyingName, jvmType)
    } else {
      ch << ALoad(0) << ACONST_NULL << PutField(className, underlyingName, jvmType)
    }
  }

  /** Initializes a (strict) field
   *  @param ch the codehandler to add the initializing code to
   *  @param className the name of the class in which the field is initialized
   *  @param field the field to be initialized
   *  @param isStatic true if this is a static field
   */
  def initStrictField(ch: CodeHandler, className: String, field: FunDef, isStatic: Boolean)(implicit locals: Locals) {
    val (_, name , _) = leonFunDefToJVMInfo(field).get
    val body = field.body.getOrElse(throw CompilationException("No body for field?"))
    val jvmType = typeToJVM(field.returnType)

    mkExpr(body, ch)

    if (isStatic){
      ch << PutStatic(className, name, jvmType)
    } else {
      ch << ALoad(0) << SWAP << PutField (className, name, jvmType)
    }
  }

  def compileAbstractClassDef(acd : AbstractClassDef) {

    val cName = defToJVMName(acd)

    val cf  = classes(acd)

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_ABSTRACT
    ).asInstanceOf[U2])

    cf.addInterface(CaseClassClass)

    // add special monitor for method invocations
    if (params.doInstrument) {
      val fh = cf.addField("I", instrumentedField)
      fh.setFlags(FIELD_ACC_PUBLIC)
    }

    val (fields, methods) = acd.methods partition { _.canBeField }
    val (strictFields, lazyFields) = fields partition { _.canBeStrictField }

    // Compile methods
    for (method <- methods) {
      compileFunDef(method,acd)
    }

    // Compile lazy fields
    for (lzy <- lazyFields) {
      compileLazyField(lzy, acd)
    }

    // Compile strict fields
    for (field <- strictFields) {
      compileStrictField(field, acd)
    }

    // definition of the constructor
    locally {
      val constrParams = if (requireMonitor) {
        Seq(monitorID -> s"L$MonitorClass;")
      } else Seq()

      val newLocs = NoLocals.withVars {
        constrParams.map(_._1).zipWithIndex.toMap.mapValues(_ + 1)
      }

      val cch = cf.addConstructor(constrParams.map(_._2) : _*).codeHandler

      for (lzy <- lazyFields) { initLazyField(cch, cName, lzy, isStatic = false)(newLocs) }
      for (field <- strictFields) { initStrictField(cch, cName, field, isStatic = false)(newLocs) }

      // Call parent constructor
      cch << ALoad(0)
      acd.parent match {
        case Some(parent) =>
          val pName = defToJVMName(parent.classDef)
          // Load monitor object
          if (requireMonitor) cch << ALoad(1)
          val constrSig = if (requireMonitor) "(L" + MonitorClass + ";)V" else "()V"
          cch << InvokeSpecial(pName, constructorName, constrSig)

        case None =>
          // Call constructor of java.lang.Object
          cch << InvokeSpecial(ObjectClass, constructorName, "()V")
      }

      // Initialize special monitor field
      if (params.doInstrument) {
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

  def instrumentedGetField(ch: CodeHandler, cct: ClassType, id: Identifier)(implicit locals: Locals): Unit = {
    val ccd = cct.classDef
    ccd.fields.zipWithIndex.find(_._1.id == id) match {
      case Some((f, i)) =>
        val expType = cct.fields(i).getType

        val cName = defToJVMName(ccd)
        if (params.doInstrument) {
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
          case TypeParameter(_) =>
            mkUnbox(expType, ch)
          case _ =>
        }
      case None =>
        throw CompilationException("Unknown field: "+ccd.id.name+"."+id)
    }
  }

  def compileCaseClassDef(ccd: CaseClassDef) {

    val cName = defToJVMName(ccd)
    val pName = ccd.parent.map(parent => defToJVMName(parent.classDef))
    // An instantiation of ccd with its own type parameters
    val cct = CaseClassType(ccd, ccd.tparams.map(_.tp))

    val cf = classes(ccd)

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    if(ccd.parent.isEmpty) {
      cf.addInterface(CaseClassClass)
    }

    // Case class parameters
    val fieldsTypes = ccd.fields.map { vd => (vd.id, typeToJVM(vd.getType)) }
    val constructorArgs = if (requireMonitor) {
      (monitorID -> s"L$MonitorClass;") +: fieldsTypes
    } else fieldsTypes

    val newLocs = NoLocals.withFields(constructorArgs.map {
      case (id, jvmt) => (id, (cName, id.name, jvmt))
    }.toMap)

    locally {
      val (fields, methods) = ccd.methods partition { _.canBeField }
      val (strictFields, lazyFields) = fields partition { _.canBeStrictField }

      // Compile methods
      for (method <- methods) {
        compileFunDef(method,ccd)
      }

      // Compile lazy fields
      for (lzy <- lazyFields) {
        compileLazyField(lzy, ccd)
      }

      // Compile strict fields
      for (field <- strictFields) {
        compileStrictField(field, ccd)
      }

      // definition of the constructor
      if(!params.doInstrument && !requireMonitor && ccd.fields.isEmpty && !ccd.methods.exists(_.canBeField)) {
        cf.addDefaultConstructor
      } else {
        for((id, jvmt) <- constructorArgs) {
          val fh = cf.addField(jvmt, id.name)
          fh.setFlags((
            FIELD_ACC_PUBLIC |
            FIELD_ACC_FINAL
          ).asInstanceOf[U2])
        }

        if (params.doInstrument) {
          val fh = cf.addField("I", instrumentedField)
          fh.setFlags(FIELD_ACC_PUBLIC)
        }

        val cch = cf.addConstructor(constructorArgs.map(_._2) : _*).codeHandler

        if (params.doInstrument) {
          cch << ALoad(0)
          cch << Ldc(0)
          cch << PutField(cName, instrumentedField, "I")
        }

        var c = 1
        for((id, jvmt) <- constructorArgs) {
          cch << ALoad(0)
          cch << (jvmt match {
            case "I" | "Z" => ILoad(c)
            case _ => ALoad(c)
          })
          cch << PutField(cName, id.name, jvmt)
          c += 1
        }

        // Call parent constructor AFTER initializing case class parameters
        if (ccd.parent.isDefined) {
          cch << ALoad(0)
          if (requireMonitor) {
            cch << ALoad(1)
            cch << InvokeSpecial(pName.get, constructorName, s"(L$MonitorClass;)V")
          } else {
            cch << InvokeSpecial(pName.get, constructorName, "()V")
          }
        } else {
          // Call constructor of java.lang.Object
          cch << ALoad(0)
          cch << InvokeSpecial(ObjectClass, constructorName, "()V")
        }

        // Now initialize fields
        for (lzy <- lazyFields) { initLazyField(cch, cName, lzy, isStatic = false)(newLocs) }
        for (field <- strictFields) { initStrictField(cch, cName , field, isStatic = false)(newLocs) }
        cch << RETURN
        cch.freeze
      }
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

      pech << Ldc(ccd.fields.size)
      pech << NewArray(ObjectClass)

      for ((f, i) <- ccd.fields.zipWithIndex) {
        pech << DUP
        pech << Ldc(i)
        pech << ALoad(0)
        instrumentedGetField(pech, cct, f.id)(newLocs)
        mkBox(f.getType, pech)(newLocs)
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
      if(ccd.fields.nonEmpty) {
        ech << ALoad(1) << CheckCast(cName) << AStore(castSlot)

        for(vd <- ccd.fields) {
          ech << ALoad(0)
          instrumentedGetField(ech, cct, vd.id)(newLocs)
          ech << ALoad(castSlot)
          instrumentedGetField(ech, cct, vd.id)(newLocs)

          typeToJVM(vd.getType) match {
            case "I" | "Z" =>
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
      hch << InvokeStatic(HashingClass, "seqHash", s"([L$ObjectClass;I)I") << DUP
      hch << ALoad(0) << SWAP << PutField(cName, hashFieldName, "I")
      hch << IRETURN

      hch.freeze
    }

  }
}
