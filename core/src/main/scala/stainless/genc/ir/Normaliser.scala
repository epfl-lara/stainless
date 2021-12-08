/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._

/*
 * Flatten out block expressions in argument-like position (e.g. function argument, while
 * condition, ...) and ensure execution order match between Scala & C execution models by
 * adding explicit execution points.
 */
final class Normaliser(val ctx: inox.Context) extends Transformer(CIR, NIR) with NoEnv {
  import from._

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  // Inject return in functions that need it
  override def recImpl(fd: FunDef)(using Env): to.FunDef = super.recImpl(fd) match {
    case fd @ to.FunDef(_, returnType, _, _, to.FunBodyAST(body), _, _) if !returnType.isUnitType =>
      val newBody = to.FunBodyAST(inject({ e => to.Return(e) }, e => !e.isInstanceOf[to.Return])(body))

      fd.body = newBody

      fd

    case fun => fun
  }

  private def recAT(typ: ArrayType)(using Env) = rec(typ).asInstanceOf[to.ArrayType]
  private def recCT(typ: ClassType)(using Env) = rec(typ).asInstanceOf[to.ClassType]

  override def recImpl(e: Expr)(using env: Env): (to.Expr, Env) = e match {
    case _: Binding | _: FunVal | _: FunRef | _: Lit | _: Block | _: Deref | _: IntegralCast => super.recImpl(e)

    case Decl(vd0, Some(ArrayInit(alloc0))) =>
      val vd = rec(vd0)

      val (preAlloc, alloc) = alloc0 match {
        case ArrayAllocStatic(typ, length, Right(values0)) =>
          val (preValues, values) = flattenArgs(false, false, values0)
          val alloc = to.ArrayAllocStatic(recAT(typ), length, Right(values))

          preValues -> alloc

        case ArrayAllocStatic(typ, length, Left(_)) =>
          val alloc = to.ArrayAllocStatic(recAT(typ), length, Left(to.Zero))

          Seq.empty -> alloc

        case ArrayAllocVLA(typ, length0, valueInit0) =>
          // Here it's fine to do two independent normalisations because there will be a
          // sequence point between the length and the value in the C code anyway.
          val (preLength, length) = flatten(length0, allowTopLevelApp = true, allowArray = false)
          val (preValueInit, valueInit) = flatten(valueInit0, allowTopLevelApp = true, allowArray = false)

          if (preValueInit.nonEmpty) {
            ctx.reporter.debug(s"VLA Elements init not supported: ${preValueInit mkString " ~ "} ~ $valueInit")
            ctx.reporter.fatalError(s"VLA elements cannot be initialised with a complex expression")
          }

          val alloc = to.ArrayAllocVLA(recAT(typ), length, valueInit)

          preLength -> alloc
      }

      val declinit = to.Decl(vd, Some(to.ArrayInit(alloc)))

      combine(preAlloc :+ declinit) -> env

    case Decl(vd0, Some(value0)) =>
      val vd = rec(vd0)
      val (pre, value) = flatten(value0, allowTopLevelApp = true, allowArray = true)
      val declinit = to.Decl(vd, Some(value))

      combine(pre :+ declinit) -> env

    case Decl(vd0, None) =>
      val vd = rec(vd0)
      val decl = to.Decl(vd, None)
      decl -> env

    case App(fun0, extra0, args0) =>
      val fun = recCallable(fun0)
      val extra = extra0 map rec // context argument are trivial enough to not require special handling
      val (preArgs, args) = flattenArgs(allowTopLevelApp = true, allowArray = false, args0)
      val app = to.App(fun, extra, args)

      combine(preArgs :+ app) -> env

    case Construct(cd0, args0) =>
      val cd = rec(cd0)
      val (preArgs, args) = flattenArgs(allowTopLevelApp = true, args0.zip(cd0.fields).map {
        case (e, vd) => (e, vd.typ.isFixedArray)
      })
      val ctor = to.Construct(cd, args)

      combine(preArgs :+ ctor) -> env

    case ai @ ArrayInit(_) => super.recImpl(ai) // this will be handled later

    case FieldAccess(obj0, fieldId) =>
      val (preObj, obj) = flatten(obj0, allowTopLevelApp = false, allowArray = false)
      val access = to.FieldAccess(obj, fieldId)

      combine(preObj :+ access) -> env

    case MemSet(pointer0, value0, size0) =>
      val (Seq(prePointer, preValue, preSize), Seq(pointer, value, size)) =
        flattenAll(allowTopLevelApp = false, allowArray = false, pointer0, value0, size0)
      val memset = to.MemSet(pointer, value, size)

      combine(prePointer ++ preValue ++ preSize :+ memset) -> env

    case SizeOf(tpe) => to.SizeOf(rec(tpe)) -> env

    case ArrayAccess(array0, index0) =>
      val (Seq(preArray, preIndex), Seq(array, index)) =
        flattenAll(allowTopLevelApp = false, allowArray = false, array0, index0)
      val access = to.ArrayAccess(array, index)

      combine(preArray ++ preIndex :+ access) -> env

    case ArrayLength(array0) =>
      val (preArray, array) = flatten(array0, allowTopLevelApp = false, allowArray = false)
      val length = to.ArrayLength(array)

      combine(preArray :+ length) -> env

    case Assign(ArrayAccess(array0, index0), rhs0) =>
      // Add sequence point for index and rhs, but we assume array is simple enough to not require normalisation.
      val (preArray, array) = flatten(array0, allowTopLevelApp = false, allowArray = false)
      val (Seq(preIndex, preRhs), Seq(index, rhs)) = flattenAll(allowTopLevelApp = false, allowArray = false, index0, rhs0)

      if (preArray.nonEmpty)
        ctx.reporter.fatalError(s"Unsupported form of array update: $e")

      val assign = to.Assign(to.ArrayAccess(array, index), rhs)

      combine(preIndex ++ preRhs :+ assign) -> env

    case assign0 @ Assign(lhs0, rhs0) =>
      val (preLhs, lhs) = flatten(lhs0, allowTopLevelApp = false, allowArray = false)

      if (preLhs.nonEmpty) {
        ctx.reporter.debug(s"When processing:\n$e")
        ctx.reporter.fatalError(s"Assumed to be invalid Scala code is apparently present in the AST:\n$assign0")
      }

      val (preRhs, rhs) = flatten(rhs0, allowTopLevelApp = false, allowArray = false)

      val assign = to.Assign(lhs, rhs)

      combine(preRhs :+ assign) -> env

    case BinOp(op, lhs0, rhs0) =>
      val (Seq(preLhs, preRhs), Seq(lhs, rhs)) = flattenAll(allowTopLevelApp = true, allowArray = false, lhs0, rhs0)

      def default = {
        val binop = to.BinOp(op, lhs, rhs)
        combine(preLhs ++ preRhs :+ binop) -> env
      }

      def short(thenn: to.Expr, elze: to.Expr) = {
        val expr = to.IfElse(lhs, thenn, elze)
        combine(preLhs :+ expr) -> env
      }

      // Handle short-circuiting
      if (preRhs.isEmpty) default
      else op match {
        case And => short(combine(preRhs :+ rhs), to.False)
        case Or => short(to.True, combine(preRhs :+ rhs))
        case _ => default
      }

    case UnOp(op, expr0) =>
      val (pre, expr) = flatten(expr0, allowTopLevelApp = true, allowArray = false)
      val unop = to.UnOp(op, expr)

      combine(pre :+ unop) -> env

    case If(cond0, thenn0) =>
      val (preCond, cond) = flatten(cond0, allowTopLevelApp = true, allowArray = false)
      val thenn = rec(thenn0)

      val fi = to.If(cond, thenn)

      combine(preCond :+ fi) -> env

    case IfElse(cond0, thenn0, elze0) =>
      val (preCond, cond) = flatten(cond0, allowTopLevelApp = true, allowArray = false)
      val thenn = rec(thenn0)
      val elze = rec(elze0)

      val fi = to.IfElse(cond, thenn, elze)

      combine(preCond :+ fi) -> env

    case While(cond0, body0) =>
      val (preCond, cond) = flatten(cond0, allowTopLevelApp = true, allowArray = false)
      val body = rec(body0)

      val loop = preCond match {
        case Seq() => to.While(cond, body)
        case preCond =>
          // Transform while ({ preCond; cond }) { body } into
          // while (true) { preCond; if (cond) { body } else { break } }
          to.While(to.True, to.buildBlock(preCond :+ to.IfElse(cond, body, to.buildBlock(to.Break :: Nil))))
      }

      loop -> env

    case Return(expr0) =>
      val (preExpr, expr) = flatten(expr0, allowTopLevelApp = true, allowArray = false)
      val res = preExpr match {
        case Seq() => to.Return(expr)
        case _ => to.buildBlock(preExpr :+ to.Return(expr))
      }

      res -> env

    case Assert(expr0) =>
      val (preExpr, expr) = flatten(expr0, allowTopLevelApp = true, allowArray = false)
      val res = preExpr match {
        case Seq() => to.Assert(expr)
        case _ => to.buildBlock(preExpr :+ to.Assert(expr))
      }

      res -> env

    case IsA(expr0, ct0) =>
      val ct = recCT(ct0)
      val (preExpr, expr) = flatten(expr0, allowTopLevelApp = false, allowArray = false)
      val isa = to.IsA(expr, ct)

      combine(preExpr :+ isa) -> env

    case AsA(expr0, ct0) =>
      val ct = recCT(ct0)
      val (preExpr, expr) = flatten(expr0, allowTopLevelApp = true, allowArray = true)
      val asa = to.AsA(expr, ct)

      combine(preExpr :+ asa) -> env

    case Ref(e0) =>
      val (pre, e) = flatten(e0, allowTopLevelApp = true, allowArray = true)
      val ref = to.Ref(e)

      combine(pre :+ ref) -> env

    case _ => ctx.reporter.fatalError(s"$e is not handled (${e.getClass}) by the normaliser")
  }

  private def combine(es: Seq[to.Expr]): to.Expr = es match {
    case Seq() => ctx.reporter.fatalError("no argument")
    case Seq(e) => e // don't introduce block if we can
    case es => to.buildBlock(es)
  }

  // In most cases, we should add an explicit sequence point when calling a function (i.e. by introducing
  // a variable holding the result of the function call). However, in a few cases this is not required;
  // e.g. when declaring a variable we can directly call a function without needing a (duplicate) sequence
  // point. Caller can therefore carefully set `allowTopLevelApp` to true in those cases.
  private def flatten(e: Expr, allowTopLevelApp: Boolean, allowArray: Boolean)(using Env): (Seq[to.Expr], to.Expr) = {
    def innerLoop(e2: to.Expr): (Seq[to.Expr], to.Expr) = e2 match {
      case to.Block(init :+ last) =>
        (init, last)
      case to.IntegralCast(e3, tpe) =>
        val (i, l) = innerLoop(e3)
        (i, to.IntegralCast(l, tpe))
      case to.AsA(e3, tpe) =>
        val (i, l) = innerLoop(e3)
        (i, to.AsA(l, tpe))
      case e =>
        (Seq.empty, e)
    }
    val (init, last) = innerLoop(rec(e))
    normalise(init, last, allowTopLevelApp, allowArray)
  }

  // Flatten all the given arguments, adding strict normalisation is needed and returning two lists of:
  //  - the init statements for each argument
  //  - the arguments themselves
  private def flattenAll(allowTopLevelApp: Boolean, allowArray: Boolean, args0: Expr*)(using Env): (Seq[Seq[to.Expr]], Seq[to.Expr]) = {
    val (initss1, args1) = args0.map(flatten(_, allowTopLevelApp, allowArray)).unzip
    val initssArgs = for (i <- 0 until args1.length) yield {
      val (argDeclOpt, arg) = strictNormalisation(args1(i), initss1:_*)
      val init = initss1(i) ++ argDeclOpt
      (init, arg)
    }

    initssArgs.unzip
  }

  private def flattenAll(allowTopLevelApp: Boolean, args0: Seq[(Expr, Boolean)])(using Env): (Seq[Seq[to.Expr]], Seq[to.Expr]) = {
    val (initss1, args1) = args0.map { case (arg0, allowArray) => flatten(arg0, allowTopLevelApp, allowArray) }.unzip
    val initssArgs = for (i <- 0 until args1.length) yield {
      val (argDeclOpt, arg) = strictNormalisation(args1(i), initss1:_*)
      val init = initss1(i) ++ argDeclOpt
      (init, arg)
    }

    initssArgs.unzip
  }

  // Extract all "init" together; first regular flatten then a strict normalisation.
  private def flattenArgs(allowTopLevelApp: Boolean, allowArray: Boolean, args0: Seq[Expr])(using Env): (Seq[to.Expr], Seq[to.Expr]) = {
    val (initss, args) = flattenAll(allowTopLevelApp, allowArray, args0:_*)
    val allInit = initss.flatten

    (allInit, args)
  }

  private def flattenArgs(allowTopLevelApp: Boolean, args0: Seq[(Expr, Boolean)])(using Env): (Seq[to.Expr], Seq[to.Expr]) = {
    val (initss, args) = flattenAll(allowTopLevelApp, args0)
    val allInit = initss.flatten

    (allInit, args)
  }

  // Simple expressions that do not require normalisation
  // We allow here function invocations where the `FunDef` is marked as `pure` thanks to
  // the effects analysis done during the `Scala2IR` phase (or thanks to user annotation)
  private def isSimple(e: to.Expr, allowTopLevelApp: Boolean, allowArray: Boolean, allowVariable: Boolean): Boolean = {
    def rec(e: to.Expr): Boolean = e match {
      case _: to.Binding => allowVariable
      case _: to.Lit => true
      case to.Deref(e0) => rec(e0)
      case to.IntegralCast(e0, _) => rec(e0)
      case to.AsA(e0, _) => rec(e0)
      case to.BinOp(op, lhs, rhs) => rec(lhs) && rec(rhs)
      case to.UnOp(op, e0) => rec(e0)
      case to.App(to.FunVal(fd), extra, args) if allowTopLevelApp => fd.isPure && extra.forall(rec) && args.forall(rec)
      case to.ArrayInit(to.ArrayAllocStatic(_, _, Left(_))) if allowArray => true
      case to.ArrayInit(to.ArrayAllocStatic(_, _, Right(elems))) if allowArray => elems.forall(rec)
      case _ => false
    }
    rec(e)
  }

  private def normalise(pre: Seq[to.Expr], value: to.Expr, allowTopLevelApp: Boolean, allowArray: Boolean): (Seq[to.Expr], to.Expr) = value match {
    case _ if isSimple(value, allowTopLevelApp, allowArray, true) => (pre, value)

    case _: to.While => (pre :+ value, to.Lit(Literals.UnitLit))

    case fi0 @ to.IfElse(_, _, _) =>
      val norm = freshNormVal(fi0.getType, isVar = true)
      val decl = to.Decl(norm, None)
      val binding = to.Binding(norm)
      val fi = inject({ e => to.Assign(binding, e) }, _ => true)(fi0)

      (pre :+ decl :+ fi, binding)

    case app @ to.App(fun, _, _) if !allowTopLevelApp =>
      // Add explicit execution point by saving the result in a temporary variable
      val norm = freshNormVal(fun.typ.ret, isVar = false)
      val declinit = to.Decl(norm, Some(app))
      val binding = to.Binding(norm)

      (pre :+ declinit, binding)

    case ai @ to.ArrayInit(_) =>
      // Attach the ArrayInit to a Decl
      // Go backwards to reuse code from the main recImpl function
      val ai0 = backward(ai)
      val norm = freshNormVal(ai.getType, isVar = false)
      val norm0 = backward(norm)
      val declinit0 = from.Decl(norm0, Some(ai0))
      val binding = to.Binding(norm)

      val (preDeclinit, declinit) = flatten(declinit0, allowTopLevelApp = false, allowArray = false)(using Ø)

      (preDeclinit :+ declinit, binding)

    case to.Assign(_, _) => ctx.reporter.fatalError("unexpected assignement")

    case value => (pre, value)
  }

  // FIXME: Not sure what this is for?
  // Strict normalisation: create a normalisation variable to save the result of an argument if it could be modified
  // by an init segment (from any argument) extracted during regular normalisation.
  private def strictNormalisation(value: to.Expr, inits: Seq[to.Expr]*): (Option[to.Decl], to.Expr) = {
    if (inits.forall(_.isEmpty) || isSimple(value, allowTopLevelApp = true, allowArray = true, allowVariable = false)) {
      // No init segment, so we can safely use the given value as is
      // Same when value is simple
      (None, value)
    } else {
      // We store the result in a temporary variable.
      val norm = freshNormVal(value.getType, isVar = false)
      val binding = to.Binding(norm)
      val declinit = to.Decl(norm, Some(value))

      (Some(declinit), binding)
    }
  }

  // Apply `action` on the AST leaf expressions.
  private def inject(action: to.Expr => to.Expr, pre: to.Expr => Boolean)(e: to.Expr): to.Expr = {
    val injecter = new Transformer(to, to) with NoEnv { injecter =>
      import injecter.from._

      override def recImpl(e: Expr)(using Env): (Expr, Env) = e match {
        case _ if !pre(e) => (e, Ø)

        case Decl(_, _) | Assign(_, _) | While(_, _) =>
          ctx.reporter.fatalError(s"Injecting into unexpected expression: $e")

        case Block(es) => (buildBlock(es.init :+ rec(es.last)), Ø)

        case If(cond, thenn) => (If(cond, rec(thenn)), Ø)

        case IfElse(cond, thenn, elze) => (IfElse(cond, rec(thenn), rec(elze)), Ø)

        case e => (action(e), Ø) // no more recursion here
      }
    }

    injecter(e)
  }

  private def freshNormVal(typ: to.Type, isVar: Boolean) = to.ValDef(freshId("norm"), typ, isVar)

  private def freshId(id: String): to.Id = id + "_" + freshCounter.next(id)

  private val freshCounter = new utils.UniqueCounter[String]()

  private val backward = new Transformer(NIR, CIR) with NoEnv
}
