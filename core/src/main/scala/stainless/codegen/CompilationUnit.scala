/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package codegen

import inox.utils.UniqueCounter
import runtime.Monitor

import cafebabe._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import java.lang.reflect.Constructor
import java.lang.reflect.InvocationTargetException

import scala.collection.mutable.{Map => MutableMap}

class CompilationUnit(val program: Program, val context: inox.Context)(using val semantics: program.Semantics) extends CodeGeneration {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  val maxSteps: Int = options.findOptionOrDefault(inox.evaluators.optMaxCalls)

  val loader = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)

  class CompiledExpression(cf: ClassFile, expression: Expr, args: Seq[ValDef]) {
    private lazy val cl = loader.loadClass(cf.className)
    private lazy val meth = cl.getMethods()(0)

    private lazy val exprType = expression.getType

    def argsToJVM(args: Seq[Expr], monitor: Monitor): Seq[AnyRef] = {
      args.map(valueToJVM(_)(using monitor))
    }

    def evalToJVM(args: Seq[AnyRef], monitor: Monitor): AnyRef = {
      val allArgs = monitor +: args
      meth.invoke(null, allArgs.toArray : _*)
    }

    def evalFromJVM(args: Seq[AnyRef], monitor: Monitor): Expr = {
      try {
        jvmToValue(evalToJVM(args, monitor), exprType)
      } catch {
        case ite: InvocationTargetException => throw ite.getCause
      }
    }

    def eval(model: program.Model)(monitor: Monitor): Expr = {
      try {
        evalFromJVM(argsToJVM(args.map(model.vars), monitor), monitor)
      } catch {
        case ite: InvocationTargetException => throw ite.getCause
      }
    }
  }

  private[this] val runtimeCounter = new UniqueCounter[Unit]

  private[this] var runtimeTypeToIdMap = Map[Type, Int]()
  private[this] var runtimeIdToTypeMap = Map[Int, Type]()
  protected def getType(id: Int): Type = synchronized(runtimeIdToTypeMap(id))
  protected def registerType(tpe: Type): Int = synchronized(runtimeTypeToIdMap.get(tpe) match {
    case Some(id) => id
    case None =>
      val id = runtimeCounter.nextGlobal
      runtimeTypeToIdMap += tpe -> id
      runtimeIdToTypeMap += id -> tpe
      id
  })

  private[this] var runtimeChooseMap = Map[Int, (Seq[ValDef], Seq[TypeParameter], Choose)]()
  protected def getChoose(id: Int): (Seq[ValDef], Seq[TypeParameter], Choose) = synchronized(runtimeChooseMap(id))
  protected def registerChoose(c: Choose, params: Seq[ValDef], tps: Seq[TypeParameter]): Int = synchronized {
    val id = runtimeCounter.nextGlobal
    runtimeChooseMap += id -> (params, tps, c)
    id
  }

  private[this] var runtimeForallMap = Map[Int, (Seq[TypeParameter], Forall)]()
  protected def getForall(id: Int): (Seq[TypeParameter], Forall) = synchronized(runtimeForallMap(id))
  protected def registerForall(f: Forall, tps: Seq[TypeParameter]): Int = synchronized {
    val id = runtimeCounter.nextGlobal
    runtimeForallMap += id -> (tps, f)
    id
  }

  // Get the Java constructor corresponding to the Case class
  private[this] val adtConstructors: MutableMap[ADTConstructor, Constructor[_]] = MutableMap.empty

  private[this] def adtConstructor(cons: ADTConstructor): Constructor[_] =
    adtConstructors.getOrElse(cons, {
      val cf = getClassCons(cons)
      val klass = loader.loadClass(cf.className)
      // This is a hack: we pick the constructor with the most arguments.
      val conss = klass.getConstructors.sortBy(_.getParameterTypes.length)
      assert(conss.nonEmpty)
      val res = conss.last
      adtConstructors(cons) = res
      res
    })

  private[this] lazy val tupleConstructor: Constructor[_] = {
    val tc = loader.loadClass("stainless.codegen.runtime.Tuple")
    val conss = tc.getConstructors.sortBy(_.getParameterTypes.length)
    assert(conss.nonEmpty)
    conss.last
  }

  /** Translates Stainless values (not generic expressions) to JVM compatible objects.
    *
    * Currently, this method is only used to prepare arguments to reflective calls.
    * This means it is safe to return AnyRef (as opposed to primitive types), because
    * reflection needs this anyway.
    */
  def valueToJVM(e: Expr)(using monitor: Monitor): AnyRef = e match {
    case Int8Literal(v)  => java.lang.Byte.valueOf(v)
    case Int16Literal(v) => java.lang.Short.valueOf(v)
    case Int32Literal(v) => java.lang.Integer.valueOf(v)
    case Int64Literal(v) => java.lang.Long.valueOf(v)
    case bi @ BVLiteral(_, _, size) => sys.error(s"NOT IMPLEMENTED");

    case BooleanLiteral(v) =>
      java.lang.Boolean.valueOf(v)

    case UnitLiteral() =>
      java.lang.Boolean.valueOf(true)

    case CharLiteral(c) =>
      Character.valueOf(c)

    case IntegerLiteral(v) =>
      new runtime.BigInt(v.toString)

    case FractionLiteral(n, d) =>
      new runtime.Rational(n.toString, d.toString)

    case StringLiteral(v) =>
      new java.lang.String(v)

    case GenericValue(tp, id) =>
      e

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(valueToJVM).toArray).asInstanceOf[AnyRef]

    case adt @ ADT(id, tps, args) =>
      val cons = adtConstructor(adt.getConstructor.definition)
      try {
        val tpeParam = if (tps.isEmpty) Seq() else Seq(tps.map(registerType).toArray)
        val jvmArgs = monitor +: (tpeParam ++ args.map(valueToJVM))
        cons.newInstance(jvmArgs.toArray : _*).asInstanceOf[AnyRef]
      } catch {
        case e : java.lang.reflect.InvocationTargetException => throw e.getCause
      }

    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    //case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType()) =>
    //  exprs.map(e => exprToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray

    case s @ FiniteSet(els, _) =>
      val s = new stainless.codegen.runtime.Set()
      for (e <- els) {
        s.insert(valueToJVM(e))
      }
      s

    case b @ FiniteBag(els, _) =>
      val b = new stainless.codegen.runtime.Bag()
      for ((k,v) <- els) {
        b.insert(valueToJVM(k), valueToJVM(v).asInstanceOf[stainless.codegen.runtime.BigInt])
      }
      b

    case m @ FiniteMap(els, dflt, _, _) =>
      val m = new stainless.codegen.runtime.Map(valueToJVM(dflt))
      for ((k,v) <- els) {
        m.insert(valueToJVM(k), valueToJVM(v))
      }
      m

    case lambda: Lambda =>
      val (l: Lambda, deps) = normalizeStructure(matchToIfThenElse(lambda, assumeExhaustive = false))
      if (deps.forall { case (_, e, conds) => isValue(e) && conds.isEmpty }) {
        val (afName, closures, tparams, consSig) = compileLambda(l, Seq.empty)
        val depsMap = deps.map { case (v, dep, _) => v.id -> valueToJVM(dep) }.toMap

        val args = closures.map { case (id, _) =>
          if (id == monitorID) monitor
          else if (id == tpsID) tparams.map(registerType).toArray
          else depsMap(id)
        }

        val lc = loader.loadClass(afName)
        val conss = lc.getConstructors.sortBy(_.getParameterTypes.length)
        assert(conss.nonEmpty)
        val lambdaConstructor = conss.last
        lambdaConstructor.newInstance(args.toArray : _*).asInstanceOf[AnyRef]
      } else {
        compileExpression(lambda, Seq.empty).evalToJVM(Seq.empty, monitor)
      }

    case f @ IsTyped(FiniteArray(elems, base), ArrayType(underlying)) =>
      import scala.reflect.ClassTag

      if (smallArrays) {
        def allocArray[A: ClassTag](f: Expr => A): Array[A] = {
          val arr = new Array[A](elems.size)
          for ((v, index) <- elems.zipWithIndex) {
            arr(index) = f(v)
          }
          arr
        }

        underlying match {
          case Int8Type() =>
            allocArray { case Int8Literal(v) => v }
          case Int16Type() =>
            allocArray { case Int16Literal(v) => v }
          case Int32Type() =>
            allocArray { case Int32Literal(v) => v }
          case Int64Type() =>
            allocArray { case Int64Literal(v) => v }
          case BooleanType() =>
            allocArray { case BooleanLiteral(b) => b }
          case UnitType() =>
            allocArray { case UnitLiteral() => true }
          case CharType() =>
            allocArray { case CharLiteral(c) => c }
          case _ =>
            allocArray(valueToJVM)
        }
      } else {
        val arr = new runtime.BigArray(elems.size)
        for ((e,i) <- elems.zipWithIndex) {
          arr.insert(i, valueToJVM(e))
        }
        arr
      }

    case a @ LargeArray(elems, default, Int32Literal(size), base) =>
      import scala.reflect.ClassTag

      if (smallArrays) {
        def allocArray[A: ClassTag](f: Expr => A): Array[A] = {
          val arr = new Array[A](size)
          val d = f(default)
          for (i <- 0 until size) arr(i) = d
          for ((index, v) <- elems) arr(index) = f(v)
          arr
        }

        val ArrayType(underlying) = a.getType
        underlying match {
          case Int8Type() =>
            allocArray { case Int8Literal(v) => v }
          case Int16Type() =>
            allocArray { case Int16Literal(v) => v }
          case Int32Type() =>
            allocArray { case Int32Literal(v) => v }
          case Int64Type() =>
            allocArray { case Int64Literal(v) => v }
          case BooleanType() =>
            allocArray { case BooleanLiteral(b) => b }
          case UnitType() =>
            allocArray { case UnitLiteral() => true }
          case CharType() =>
            allocArray { case CharLiteral(c) => c }
          case _ =>
            allocArray(valueToJVM)
        }
      } else {
        val arr = new runtime.BigArray(size, valueToJVM(default))
        for ((i,e) <- elems) {
          arr.insert(i, valueToJVM(e))
        }
        arr
      }

    case _ =>
      throw CompilationException(s"Unexpected expression $e in valueToJVM")
  }

  /** Translates JVM objects back to Stainless values of the appropriate type */
  def jvmToValue(e: AnyRef, tpe: Type): Expr = (e, tpe) match {
    case (b: java.lang.Byte,    Int8Type())  => Int8Literal(b.toByte)
    case (s: java.lang.Short,   Int16Type()) => Int16Literal(s.toShort)
    case (i: java.lang.Integer, Int32Type()) => Int32Literal(i.toInt)
    case (l: java.lang.Long,    Int64Type()) => Int64Literal(l.toLong)
    case (bv: runtime.BitVector, BVType(signed, size)) => BVLiteral(signed, BigInt(bv.toBigInteger), size)

    case (c: runtime.BigInt, IntegerType()) =>
      IntegerLiteral(c.toScala)

    case (c: runtime.Rational, RealType()) =>
      val num = BigInt(c.numerator)
      val denom = BigInt(c.denominator)
      FractionLiteral(num, denom)

    case (b: java.lang.Boolean, BooleanType()) =>
      BooleanLiteral(b.booleanValue)

    case (c: java.lang.Character, CharType()) =>
      CharLiteral(c.toChar)

    case (c: java.lang.String, StringType()) =>
      StringLiteral(c)

    case (cons: runtime.ADT, adt: ADTType) =>
      val fields = cons.productElements()

      // identify case class type of ct
      jvmClassNameToCons(cons.getClass.getName) match {
        case Some(cons) =>
          val exFields = (fields zip getConstructor(cons.id, adt.tps).fields.map(_.getType)).map {
            case (e, tpe) => jvmToValue(e, tpe)
          }.toSeq
          ADT(cons.id, adt.tps, exFields)
        case _ =>
          throw CompilationException("Unable to identify class "+cons.getClass.getName+" to descendant of "+adt)
      }

    case (tpl: runtime.Tuple, tpe) =>
      val stpe = unwrapTupleType(tpe, tpl.getArity())
      val elems = stpe.zipWithIndex.map { case (tpe, i) =>
        jvmToValue(tpl.get(i), tpe)
      }
      tupleWrap(elems)

    case (gv @ GenericValue(gtp, id), tp: TypeParameter) =>
      if (gtp == tp) gv
      else GenericValue(tp, id).copiedFrom(gv)

    case (set: runtime.Set, SetType(b)) =>
      FiniteSet(set.getElements.map(jvmToValue(_, b)).toSeq, b)

    case (bag: runtime.Bag, BagType(b)) =>
      FiniteBag(bag.getElements().map { case (key, value) =>
        (jvmToValue(key, b), jvmToValue(value, IntegerType()))
      }.toSeq, b)

    case (map: runtime.Map, MapType(from, to)) =>
      val pairs = map.getElements.map { case (key, value) =>
        (jvmToValue(key, from), jvmToValue(value, to))
      }.toSeq
      val default = jvmToValue(map.default, to)
      FiniteMap(pairs, default, from, to)

    case (lambda: runtime.Lambda, _: FunctionType) =>
      val cls = lambda.getClass
      val l = jvmClassNameToLambda(cls.getName).get

      val tparams: Seq[TypeParameter] = {
        var tpSeq: Seq[TypeParameter] = Seq.empty
        object collector extends ConcreteStainlessSelfTreeTraverser {
          override def traverse(tpe: Type): Unit = tpe match {
            case tp: TypeParameter => tpSeq :+= tp
            case _ => super.traverse(tpe)
          }
        }
        collector.traverse(l)
        tpSeq.distinct
      }

      val tpLambda = if (tparams.isEmpty) {
        l
      } else {
        val arr = lambda.getClass.getField(tpsID.uniqueName).get(lambda).asInstanceOf[Array[Int]]
        val tps = arr.toSeq.map(getType)
        typeOps.instantiateType(l, (tparams zip tps).toMap)
      }

      val closures = exprOps.variablesOf(tpLambda).toSeq.sortBy(_.id.uniqueName)
      val closureVals = closures.map { v =>
        val fieldVal = lambda.getClass.getField(v.id.uniqueName).get(lambda)
        jvmToValue(fieldVal, v.getType)
      }

      exprOps.replaceFromSymbols((closures zip closureVals).toMap, tpLambda)

    case (_, UnitType()) =>
      UnitLiteral()

    case (ar: Array[_], ArrayType(base)) if smallArrays =>
      val elems = for (e <- ar.toSeq) yield jvmToValue(e.asInstanceOf[AnyRef], base)
      FiniteArray(elems, base)

    case (ar: runtime.BigArray, ArrayType(base)) =>
      val elems = ar.getElements.map { case (index: Int, value) =>
        index -> jvmToValue(value, base)
      }.toSeq.sortBy(_._1)
      if (elems.size == ar.size) {
        FiniteArray(elems.map(_._2), base)
      } else {
        val default = jvmToValue(ar.default, base)
        LargeArray(elems.toMap, default, Int32Literal(ar.size), base)
      }

    case _ =>
      throw CompilationException("Unsupported return value : " + e.getClass +" while expecting "+tpe)
  }


  def compileExpression(e: Expr, args: Seq[ValDef]): CompiledExpression = {
    if (e.getType == Untyped) {
      throw new UnsupportedTree(e, s"Cannot compile untyped expression.")
    }

    val id = exprCounter.nextGlobal

    val cName = "Stainless$CodeGen$Expr$"+id

    val cf = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    val argsTypes = args.map(a => typeToJVM(a.getType))

    val realArgs = ("L" + MonitorClass + ";") +: argsTypes

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

    val newMapping = Map(monitorID -> 0) ++ args.zipWithIndex.map {
      case (v, i) => v.id -> (i + 1)
    }.toMap

    mkExpr(e, ch)(using NoLocals.withVars(newMapping))

    e.getType match {
      case JvmIType() =>
        ch << IRETURN
      case Int64Type() =>
        ch << LRETURN
      case _ =>
        ch << ARETURN
    }

    ch.freeze

    synchronized(loader.register(cf))

    new CompiledExpression(cf, e, args)
  }

  val classes = compile()
  for (cf <- classes) loader.register(cf)

  def writeClassFiles(prefix: String): Unit = {
    for (cf <- classes) {
      cf.writeToFile(prefix + cf.className + ".class")
    }
  }
}

private [codegen] object exprCounter extends UniqueCounter[Unit]
private [codegen] object forallCounter extends UniqueCounter[Unit]

