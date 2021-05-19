/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction._
import extraction.throwing.trees._

import inox.utils.Position

import ExtraOps._

import ir.{ PrimitiveTypes => PT, Literals => L, Operators => O }
import ir.IRs.{ CIR }

import scala.collection.mutable.{ Map => MutableMap }

/*
 * This phase takes a set of definitions (the Dependencies) and the fonction context database (FunCtxDB)
 * and produces an equivalent program expressed in the intermediate representation without generic types (CIR).
 *
 * NOTE This phase also rejects fragment of Scala that are not supported by GenC, such as returning
 *      or copying arrays, constructing a case class with mutable fields from function arguments,
 *      the >> operator, some forms of membership tests, the unapply pattern matching construct,
 *      and more.
 */
trait Scala2IRPhase extends LeonPipeline[(Dependencies, FunCtxDB), CIR.Prog] {
  val name = "Scala to IR converter"

  implicit val debugSection = DebugSectionGenC

  def run(input: (Dependencies, FunCtxDB)): CIR.Prog = {
    val (deps, ctxDB) = input
    implicit val syms = deps.syms

    val impl = new S2IRImpl(context, ctxDB, deps)
    impl.run()

    CIR.Prog(
      impl.funResults.values.toList,
      impl.classResults.values.toList
    )
  }

}


private class S2IRImpl(val context: inox.Context, val ctxDB: FunCtxDB, val deps: Dependencies)(implicit val syms: Symbols)
  extends extraction.imperative.EffectsAnalyzer
  with IdentityFunctions
  with IdentitySorts
  with oo.IdentityClasses
  with oo.IdentityTypeDefs { self =>

  import context._

  val s: extraction.throwing.trees.type = extraction.throwing.trees
  val t: extraction.throwing.trees.type = extraction.throwing.trees

  implicit val debugSection = DebugSectionGenC
  private val prog = inox.Program(extraction.throwing.trees)(syms)
  private val evaluator = new {
    val context = self.context
    val program: prog.type = prog
    val semantics = new inox.Semantics {
      val trees: throwing.trees.type = throwing.trees
      val symbols: syms.type = syms
      val program: prog.type = prog
      def createEvaluator(ctx: inox.Context) = ???
      def createSolver(ctx: inox.Context) = ???
    }
  } with evaluators.RecursiveEvaluator
    with inox.evaluators.HasDefaultGlobalContext
    with inox.evaluators.HasDefaultRecContext

  type TransformerContext = EffectsAnalysis
  private val analysis = new {
    val symbols = syms
  } with EffectsAnalysis
  def getContext(sym: Symbols) = analysis

  object TopLevelAnds {
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case And(exprs) => Some(exprs.flatMap(unapply).flatten)
      case e => Some(Seq(e))
    }
  }

  object EvalBV {
    def unapply(expr: Expr): Option[BVLiteral] = {
      evaluator.eval(expr) match {
        case inox.evaluators.EvaluationResults.Successful(bv: BVLiteral) => Some(bv)
        case _ => None
      }
    }
  }

  /****************************************************************************************************
   *                                                       Entry point of conversion                  *
   ****************************************************************************************************/

  def run(): Unit = {
    for (df <- deps.deps) {
      df match {
        case fd: FunDef if fd.isExported =>
          rec(Outer(fd), Seq())(Map.empty, (Map.empty, Map.empty))
        case cd: ClassDef if cd.isExported =>
          rec(cd.typed.toType)(Map.empty)
        case _ =>
      }
    }
  }

  /****************************************************************************************************
   *                                                       Caches                                     *
   ****************************************************************************************************/

  // For functions, we associate each TypedFunDef to a CIR.FunDef for each "type context" (TypeMapping).
  // This is very important for (non-generic) functions nested in a generic function because for N
  // instantiation of the outer function we have only one TypedFunDef for the inner function.
  val funResults = MutableMap[(FunAbstraction, Seq[Type], TypeMapping), CIR.FunDef]()

  // The `classResults` might be queried with a generic class type, which is why we keep the concrete
  // type mapping in the cache key
  val classResults = MutableMap[(ClassType, TypeMapping), CIR.ClassDef]()



  /****************************************************************************************************
   *                                                       Helper functions                           *
   ****************************************************************************************************/
  // When converting expressions, we keep track of the variable in scope to build Bindings
  // Also, the identifier might not have the correct type (e.g. when generic). We therefore
  // need an external *concrete* type.
  private type Env = (Map[(ValDef, Type), CIR.ValDef], Map[Identifier, LocalFunDef])

  // Keep track of generic to concrete type mapping
  private type TypeMapping = Map[TypeParameter, Type]

  private def instantiate(typ: Type, tm: TypeMapping): Type =
    typeOps.instantiateType(typ, tm)

  // Here, when contexts are translated, there might remain some generic types. We use `tm` to make them disapear.
  private def convertVarInfoToArg(vi: VarInfo)(implicit tm: TypeMapping) = CIR.ValDef(rec(vi.vd.id), rec(vi.typ), vi.isVar)
  private def convertVarInfoToParam(vi: VarInfo)(implicit tm: TypeMapping) = CIR.Binding(convertVarInfoToArg(vi))

  // Extract the ValDef from the known one
  private def buildBinding(vd: ValDef)(implicit env: Env, tm: TypeMapping): CIR.Binding = {
    val typ = instantiate(vd.tpe, tm)
    val optVd = env._1.get(vd -> typ)
    val newVD = optVd match {
      case Some(vd2) => vd2
      case None =>
        // Identifiers in Leon are known to be tricky when it comes to unique id.
        // It sometimes happens that the unique id are not in sync, especially with
        // generics. Here we try to find the best match based on the name only.
        reporter.warning(s"Working around issue with identifiers on ${vd.id}...")
        env._1.collectFirst {
          case ((eid, etype), evd) if eid.id.name == vd.id.name && etype == typ => evd
        } getOrElse {
           reporter.fatalError(vd.getPos, s"Couldn't find a ValDef for ${vd.id} in the environment:\n$env")
        }
    }
    CIR.Binding(newVD)
  }

  private def buildLet(x: ValDef, e: Expr, body: Expr, isVar: Boolean)
                      (implicit env: Env, tm: TypeMapping): CIR.Expr = {
    val vd = CIR.ValDef(rec(x.id), rec(x.tpe), isVar)
    val decl = CIR.DeclInit(vd, rec(e))
    val newValDefEnv = env._1 + ((x, instantiate(x.tpe, tm)) -> vd)
    val rest = rec(body)((newValDefEnv, env._2), tm)

    CIR.buildBlock(Seq(decl, rest))
  }

  // // Include the "nesting path" in case of generic functions to avoid ambiguity
  // private def buildId(tfd: TypedFunDef)(implicit tm: TypeMapping): CIR.Id =
  //   rec(tfd.fd.id) + (if (tfd.tps.nonEmpty) buildIdPostfix(tfd.tps) else buildIdFromTypeMapping(tm))

  // Include the "nesting path" in case of generic functions to avoid ambiguity
  private def buildId(fa: FunAbstraction, tps: Seq[Type])(implicit tm: TypeMapping): CIR.Id = {
    val exported = fa.isInstanceOf[Outer] && fa.asInstanceOf[Outer].fd.isExported
    rec(fa.id, withUnique = !exported) + (if (tps.nonEmpty) buildIdPostfix(tps) else buildIdFromTypeMapping(tm))
  }

  private def buildId(ct: ClassType)(implicit tm: TypeMapping): CIR.Id = {
    val exported = ct.tcd.cd.isExported
    rec(ct.tcd.id, withUnique = !exported) + buildIdPostfix(ct.tps)
  }

  private def buildIdPostfix(tps: Seq[Type])(implicit tm: TypeMapping): CIR.Id = if (tps.isEmpty) "" else {
    "_" + (tps filterNot { _ == Untyped } map rec map CIR.repId mkString "_")
  }

  private def buildIdFromTypeMapping(tm: TypeMapping): CIR.Id = if (tm.isEmpty) "" else {
    "_" + (tm.values map { t => CIR.repId(rec(t)(tm)) } mkString "_")
  }

  // Check validity of the operator
  //
  // NOTE the creation of equals functions for `==` is deferred to a later phase.
  private def checkOp(op: O.Operator, ops: Seq[CIR.Type], pos: Position): Unit = {
    assert(ops.nonEmpty)

    def check(b: Boolean) = if (!b) {
      reporter.fatalError(pos, s"Invalid use of operator $op with the given operands")
    }

    def isLogical: Boolean = ops forall { _.isLogical }
    def isIntegral: Boolean = ops forall { _.isIntegral }
    def isPairOfT: Boolean = (ops.size == 2) && (ops forall { _ == ops(0) }) // or use <=???

    op match {
      case _: O.FromPairOfT => check(isPairOfT)
      case _: O.FromLogical => check(isLogical)
      case _: O.FromIntegral => check(isIntegral)
      case _ => reporter.fatalError(pos, s"Unhandled check of operator $op")
    }
  }

  // Prevent some form of aliasing that verification supports but our memory model doesn't.
  // See Chapter 4: Memory, Aliasing & Mutability Models For GenC
  //     of Extending Safe C Support In Leon.
  private def checkConstructArgs(args: Seq[(CIR.Expr, Position)]): Unit = {
    // Reject arguments that have mutable type (but allow var, and arrays)
    def isRefToMutableVar(arg: (CIR.Expr, Position)): Boolean = arg._1 match {
      case CIR.Binding(vd) => vd.getType.isMutable && !vd.getType.isArray
      case _ => false
    }

    args find isRefToMutableVar match {
      case Some((_, pos)) =>
        reporter.fatalError(pos, s"Invalid reference: cannot construct an object from a mutable variable.")

      case _ =>
    }
  }

  private def buildBinOp(lhs0: Expr, op: O.BinaryOperator, rhs0: Expr)
                        (pos: Position)
                        (implicit env: Env, tm: TypeMapping) = {
    val lhs = rec(lhs0)
    val rhs = rec(rhs0)

    checkOp(op, Seq(lhs.getType, lhs.getType), pos)

    CIR.BinOp(op, lhs, rhs)
  }

  private def buildUnOp(op: O.UnaryOperator, expr0: Expr)
                       (pos: Position)
                       (implicit env: Env, tm: TypeMapping) = {
    val expr = rec(expr0)

    checkOp(op, Seq(expr.getType), pos)

    CIR.UnOp(op, expr)
  }

  // Create a binary AST
  private def buildMultiOp(op: O.BinaryOperator, exprs: Seq[Expr])
                          (pos: Position)
                          (implicit env: Env, tm: TypeMapping): CIR.BinOp = exprs.toList match {
    case Nil => reporter.fatalError(pos, "no operands")
    case a :: Nil => reporter.fatalError(pos, "at least two operands required")
    case a :: b :: Nil => buildBinOp(a, op, b)(pos)
    case a :: xs => CIR.BinOp(op, rec(a), buildMultiOp(op, xs)(pos))
  }

  // Tuples are converted to classes
  private def tuple2Class(typ: Type)(implicit tm: TypeMapping): CIR.ClassDef = typ match {
    case TupleType(bases) =>
      val types = bases map rec
      val fields = types.zipWithIndex map { case (typ, i) => CIR.ValDef("_" + (i+1), typ, isVar = false) }
      val id = "Tuple" + buildIdPostfix(bases)
      CIR.ClassDef(id, None, fields, isAbstract = false, isExported = false)

    case _ => reporter.fatalError(typ.getPos, s"Unexpected ${typ.getClass} instead of TupleType")
  }

  private def castNotSupported(ct: ClassType): Boolean =
    ct.tcd.cd.isAbstract && ct.tcd.parents.nonEmpty

  /****************************************************************************************************
   *                                                       Pattern Matching helper functions          *
   ****************************************************************************************************/
  // NOTE We don't rely on ExprOps.matchToIfThenElse because it doesn't apply well with
  //      side-effects and type casting.

  private case class PMCase(cond: CIR.Expr, guardOpt: Option[CIR.Expr], body: CIR.Expr) {
    def fullCondition: CIR.Expr = guardOpt match {
      case None => cond
      case Some(guard) if cond == CIR.True => guard
      case Some(guard) => CIR.BinOp(O.And, cond, guard)
    }
  }

  private object ElseCase {
    def unapply(caze: PMCase): Option[CIR.Expr] = {
      if (CIR.True == caze.fullCondition) Some(caze.body)
      else None
    }
  }

  private def convertPatMap(scrutinee0: Expr, cases0: Seq[MatchCase])(implicit env: Env, tm: TypeMapping): CIR.Expr = {
    require(cases0.nonEmpty)

    def withTmp(typ: Type, value: Expr, env: Env): (Variable, Some[CIR.DeclInit], Env) = {
      val tmp0 = ValDef.fresh("tmp", typ)
      val tmpId = rec(tmp0.id)
      val tmpTyp = rec(typ)
      val tmp = CIR.ValDef(tmpId, tmpTyp, isVar = false)
      val pre = CIR.DeclInit(tmp, rec(value)(env, tm))
      val newValDefEnv = env._1 + ((tmp0, instantiate(typ, tm)) -> tmp)

      (tmp0.toVariable, Some(pre), (newValDefEnv, env._2))
    }

    def scrutRec(scrutinee0: Expr): (Expr, Option[CIR.Expr], Env) = scrutinee0 match {
      case v: Variable => (v, None, env)

      case Block(Nil, v: Variable) => (v, None, env)
      case Block(init, v: Variable) => (v, Some(rec(Block(init.init, init.last))), env)

      // case field @ CaseClassSelector(_, _: Variable, _) => (field, None, env)
      case field @ ADTSelector(_, _) => (field, None, env)

      case select @ ArraySelect(_: Variable, _: Variable | _: BVLiteral) => (select, None, env)
      case select @ ArraySelect(array: Variable, index) =>
        // Save idx into a temporary variable, but apply patmat on array access.
        // This way, the index is computed once only.
        val (newIndex, preOpt, newEnv) = withTmp(BVType(true, 32), index, env)
        val newSelect = ArraySelect(array, newIndex)
        (newSelect, preOpt, newEnv)

      case select @ ArraySelect(a, i) =>
        reporter.fatalError(scrutinee0.getPos, s"array select $a[$i] is not supported by GenC (${a.getClass}, ${i.getClass})")

      case Assert(_, _, body) => scrutRec(body)
      case Assume(_, body) => scrutRec(body)

      case _: Application | _: FunctionInvocation | _: ADT | _: LetVar | _: Let | _: Tuple | _: IfExpr =>
        withTmp(scrutinee0.getType, scrutinee0, env)

      case e => reporter.fatalError(e.getPos, s"scrutinee ${e.asString} (${e.getClass}) is not supported by GenC")
    }

    val (scrutinee, preOpt, newEnv) = scrutRec(scrutinee0)

    val cases = cases0 map { caze => convertCase(scrutinee, caze)(newEnv, tm) }

    // Identify the last case
    val last = cases.last match {
      case ElseCase(body) => body
      case caze => CIR.If(caze.fullCondition, caze.body)
    }

    // Combine all cases, using a foldRight
    val patmat = cases.init.foldRight(last) { case (caze, acc) =>
      CIR.IfElse(caze.fullCondition, caze.body, acc)
    }

    preOpt match {
      case None => patmat
      case Some(pre) => CIR.buildBlock(pre :: patmat :: Nil)
    }
  }

  // Substitute a binder (vd) by the scrutinee (or a more appropriate expression) in the given expression
  private def substituteBinder(vd: ValDef, replacement: Expr, expr: Expr): Expr =
    exprOps.replaceFromSymbols(Map(vd -> replacement), expr)

  private def buildConjunction(exprs: Seq[CIR.Expr]): CIR.Expr = exprs.foldRight[CIR.Expr](CIR.True) { case (e, acc) =>
    if (e == CIR.True) acc // Don't add trivialities in the conjunction
    else if (acc == CIR.True) e
    else CIR.BinOp(O.And, e, acc)
  }

  // Extract the condition, guard and body (rhs) of a match case
  private def convertCase(initialScrutinee: Expr, caze: MatchCase)(implicit env: Env, tm: TypeMapping): PMCase = {
    // We need to keep track of binder (and binders in sub-patterns) and their appropriate
    // substitution. We do so in an Imperative manner with variables -- sorry FP, but it's
    // much simpler that way! However, to encapsulate things a bit, we use the `update`
    // function to update both the guard and rhs safely. When we have finished converting
    // every cases, we'll be able to convert the guard and rhs to IR.
    var guardOpt = caze.optGuard
    var body = caze.rhs

    def update(binderOpt: Option[ValDef], replacement: Expr): Unit = binderOpt match {
      case Some(binder) =>
        guardOpt = guardOpt map { guard => substituteBinder(binder, replacement, guard) }
        body = substituteBinder(binder, replacement, body)

      case None => ()
    }

    // For the main pattern and its subpatterns, we keep track of the "current" scrutinee
    // expression (after cast, field access, and other similar operations).
    def ccRec(pat: Pattern, scrutinee: Expr): CIR.Expr = pat match {
      case InstanceOfPattern(b, ct) =>
        val cast = AsInstanceOf(scrutinee, ct)
        update(b, cast)

        rec(IsInstanceOf(scrutinee, ct))

      case WildcardPattern(b) =>
        update(b, scrutinee)
        CIR.True

      case ClassPattern(b, ct, subs) =>
        val (checkType, cast) =
          if (scrutinee.getType == ct) CIR.True -> scrutinee // Omit useless type checks & casts
          else rec(IsInstanceOf(scrutinee, ct)) -> AsInstanceOf(scrutinee, ct)

        update(b, cast)

        // Use the classDef fields to have the original identifiers!
        val checkSubs = (ct.tcd.fields zip subs) map { case (field, sub) =>
          ccRec(sub, ClassSelector(cast, field.id))
        }

        // Luckily, there are no block involved so we can have a simple conjunction
        buildConjunction(checkType +: checkSubs)

      case TuplePattern(b, subs) =>
        // Somewhat similar to CaseClassPattern, but simpler
        update(b, scrutinee)

        val checkSubs = subs.zipWithIndex map { case (sub, index) =>
          ccRec(sub, TupleSelect(scrutinee, index+1))
        }

        buildConjunction(checkSubs)

      case LiteralPattern(b, lit) =>
        update(b, scrutinee)
        buildBinOp(scrutinee, O.Equals, lit)(pat.getPos)

      case UnapplyPattern(_, _, _, _, _) =>
        reporter.fatalError(pat.getPos, s"Unapply Pattern, a.k.a. Extractor Objects, is not supported by GenC")
    }

    val cond = ccRec(caze.pattern, initialScrutinee)

    PMCase(cond, guardOpt map rec, rec(body))
  }



  /****************************************************************************************************
   *                                                       Recursive conversion                       *
   ****************************************************************************************************/
  private def rec(id: Identifier, withUnique: Boolean = true): CIR.Id = {
    if (withUnique) id.uniqueNameDelimited("_")
    else id.name
  }

  // Try first to fetch the function from cache to handle recursive funcitons.
  private def rec(fa: FunAbstraction, tps: Seq[Type])(implicit tm0: TypeMapping, env: Env): CIR.FunDef = {
    val cacheKey = (fa, tps, tm0)
    funResults get cacheKey getOrElse {

    val id = buildId(fa, tps)(tm0)

    val ctxDBAbs = fa match {
      case Outer(_) => Seq()
      case Inner(lfd) => ctxDB(lfd)
    }

    val export = fa match {
      case Outer(fd) if fd.isExported => true
      case _ => false
    }

    val tpSubst: TypeMapping = (fa.tparams.map(_.tp) zip tps).toMap.filter(tt => tt._1 != tt._2)

    // Warn user about recursivity: this is not MISRA compliant unless it is very tightly controlled.
    // NOTE this check is done after VC are removed.

    // FIXME: Add this warning
    // if (tfd.fd.isRecursive(deps.syms))
      // reporter.warning(s"MISRA rules state that recursive functions should be very tightly controlled; ${tfd.id} is recursive")

    // We have to manually specify tm1 from now on to avoid using tm0. We mark tm1 as
    // implicit as well to generate ambiguity at compile time to avoid forgetting a call site.
    implicit val tm1: TypeMapping = tm0 ++ tpSubst

    // Make sure to get the id from the function definition, not the typed one, as they don't always match.
    val nonGhostParams = fa.params.filter(!_.flags.contains(Ghost))
    val paramTypes = nonGhostParams map { p => rec(p.getType)(tm1) }
    val paramIds = nonGhostParams map { p => rec(p.id) }
    val params = (paramIds zip paramTypes) map { case (id, typ) => CIR.ValDef(id, typ, isVar = false) }

    // Extract the context for the function definition, taking care of the remaining generic types in the context.

    val funCtx = ctxDBAbs map { c => convertVarInfoToArg(c)(tm1) }

    val returnType = rec(fa.returnType)(tm1)
    if (returnType.containsArray)
      reporter.fatalError(fa.getPos, "Returning arrays from function is not supported by GenC")

    val isPure = fa.flags.contains(IsPure) || analysis.effects(fa.fullBody).isEmpty

    // Build a partial function without body in order to support recursive functions
    val fun = CIR.FunDef(id, returnType, funCtx, params, null, export, isPure)

    funResults.update(cacheKey, fun) // Register with the callee TypeMapping, *not* the newer

    // Now proceed with the body
    val body: CIR.FunBody =
      if (fa.isManuallyDefined) {
        val impl = fa.getManualDefinition
        CIR.FunBodyManual(impl.includes, impl.code)
      } else {
        // Build the new environment from context and parameters
        val ctxKeys: Seq[(ValDef, Type)] = ctxDBAbs map { c => c.vd -> instantiate(c.typ, tm1) }
        val ctxEnv: Seq[((ValDef, Type), CIR.ValDef)] = ctxKeys zip funCtx

        val paramKeys: Seq[(ValDef, Type)] = nonGhostParams map { p => p -> instantiate(p.getType, tm1) }
        val paramEnv: Seq[((ValDef, Type), CIR.ValDef)] = paramKeys zip params

        val newValDefEnv = env._1 ++ ctxEnv ++ paramEnv

        // Recurse on the FunDef body, and not the TypedFunDef one, in order to keep the correct identifiers.
        CIR.FunBodyAST(rec(fa.fullBody)((newValDefEnv, env._2), tm1))
      }

    // Now that we have a body, we can fully build the FunDef
    fun.body = body

    fun
  }}

  // We need a type mapping only when converting context argument to remove the remaining generics.
  private def rec(typ: Type)(implicit tm: TypeMapping): CIR.Type = typ match {
    case UnitType() => CIR.PrimitiveType(PT.UnitType)
    case BooleanType() => CIR.PrimitiveType(PT.BoolType)

    case BVType(true, 8) => CIR.PrimitiveType(PT.Int8Type)
    case BVType(true, 16) => CIR.PrimitiveType(PT.Int16Type)
    case BVType(true, 32) => CIR.PrimitiveType(PT.Int32Type)
    case BVType(true, 64) => CIR.PrimitiveType(PT.Int64Type)

    case BVType(false, 8) => CIR.PrimitiveType(PT.UInt8Type)
    case BVType(false, 16) => CIR.PrimitiveType(PT.UInt16Type)
    case BVType(false, 32) => CIR.PrimitiveType(PT.UInt32Type)
    case BVType(false, 64) => CIR.PrimitiveType(PT.UInt64Type)

    case CharType() => CIR.PrimitiveType(PT.CharType)
    case StringType() => CIR.PrimitiveType(PT.StringType)

    // For both case classes and abstract classes:
    case ct: ClassType =>
      val tcd = ct.tcd
      val cd = tcd.cd
      if (cd.isDropped) {
        CIR.DroppedType
      } else if (cd.isManuallyTyped) {
        val typeDef = cd.getManualType
        CIR.TypeDefType(cd.id.name, typeDef.alias, typeDef.include, cd.isExported)
      } else {
        CIR.ClassType(rec(ct))
      }

    case ArrayType(base) => CIR.ArrayType(rec(base), None)

    case TupleType(_) => CIR.ClassType(tuple2Class(typ))

    case FunctionType(from, to) => CIR.FunType(ctx = Nil, params = from map rec, ret = rec(to))

    case tp: TypeParameter => rec(instantiate(tp, tm))

    case t => reporter.fatalError(t.getPos, s"Type tree ${t.asString} (${t.getClass}) not handled by GenC component")
  }

  private def rec(ct: ClassType)(implicit tm: TypeMapping): CIR.ClassDef = {
    val cacheKey = (ct, tm)
    classResults.getOrElseUpdate(cacheKey, {
    // Convert the whole class hierarchy to register all siblings, in a top down fasion, that way
    // each children class in the the CIR hierarchy get registered to its parent and we can keep track
    // of all of them.

    type Translation = Map[ClassType, CIR.ClassDef]

    def recTopDown(ct: ClassType, parent: Option[CIR.ClassDef], acc: Translation): Translation = {
      val tcd = ct.tcd
      val cd = tcd.cd
      val id = buildId(ct)

      if (cd.isDropped || cd.isManuallyTyped)
        reporter.fatalError(ct.getPos, s"${ct.id.asString} is not convertible to ClassDef in GenC")

      if (cd.isCaseObject)
        reporter.fatalError(ct.getPos, s"Case objects (${ct.id.asString}) are not convertible to ClassDef in GenC")

      // disable name mangling for fields of exported classes
      val mangling = !cd.isExported

      // Use the class definition id, not the typed one as they might not match.
      val nonGhostFields = tcd.fields.filter(!_.flags.contains(Ghost))

      val arrayLengths: Seq[(Identifier, Int)] = cd.flags
        .find(_.isInstanceOf[HasADTInvariant]).toSeq.flatMap {
          case HasADTInvariant(inv) =>
            val invFd = syms.getFunction(inv)
            val Seq(tthisVd) = invFd.params
            val TopLevelAnds(conjuncts) = invFd.fullBody
            conjuncts.collect(e => e match {
              case Equals(ArrayLength(ClassSelector(tthis: Variable, array)), EvalBV(bv))
                if tthisVd.id == tthis.id && nonGhostFields.map(_.id).contains(array) =>

                array -> bv.toBigInt.toInt
            })
        }

      if (arrayLengths.map(_._1).toSet.size != arrayLengths.length) {
        reporter.fatalError(cd.getPos, "Cannot specify two lengths for an array in a class invariant")
      }

      val arrayLengthsMap: Map[Identifier, Int] = arrayLengths.toMap

      val fields = nonGhostFields.map(vd => vd.tpe match {
        case ArrayType(base) if arrayLengthsMap.contains(vd.id) =>
          CIR.ValDef(rec(vd.id, withUnique = mangling), CIR.ArrayType(rec(base), Some(arrayLengthsMap(vd.id))), vd.flags.contains(IsVar))
        case typ =>
          CIR.ValDef(rec(vd.id, withUnique = mangling), rec(typ), vd.flags.contains(IsVar))
      })

      val clazz = CIR.ClassDef(id, parent, fields, cd.isAbstract, cd.isExported)

      val newAcc = acc + (ct -> clazz)

      // Recurse down
      val children = cd.children map { _.typed(ct.tps) }
      children.foldLeft(newAcc) { case (currentAcc, child) => recTopDown(child.toType, Some(clazz), currentAcc) }
    }

    val translation = recTopDown(syms.getClass(root(ct.id)).typed(ct.tps).toType, None, Map.empty)

    translation(ct)
    })
  }

  private def rec(e: Expr)(implicit env: Env, tm0: TypeMapping): CIR.Expr = e match {

    case Annotated(body, _) => rec(body)

    // Casts introduced by Stainless with an assumption
    case Assume(IsInstanceOf(expr1, tpe1), Annotated(AsInstanceOf(expr2, tpe2), flags))
      if flags.contains(Unchecked) && expr1 == expr2 && tpe1 == tpe2 =>
      rec(expr1)

    /* Ignore static assertions */
    case Require(_, body) => rec(body)
    case Decreases(_, body) => rec(body)
    case Ensuring(body, _) => rec(body)
    case Assert(_, _, body) => rec(body)
    case Assume(_, body) => rec(body)

    case UnitLiteral() => CIR.Lit(L.UnitLit)
    case BooleanLiteral(v) => CIR.Lit(L.BoolLit(v))

    case bv@BVLiteral(true, _, 8) => CIR.Lit(L.Int8Lit(bv.toBigInt))
    case bv@BVLiteral(true, _, 16) => CIR.Lit(L.Int16Lit(bv.toBigInt))
    case bv@BVLiteral(true, _, 32) => CIR.Lit(L.Int32Lit(bv.toBigInt))
    case bv@BVLiteral(true, _, 64) => CIR.Lit(L.Int64Lit(bv.toBigInt))

    case bv@BVLiteral(false, _, 8) => CIR.Lit(L.UInt8Lit(bv.toBigInt))
    case bv@BVLiteral(false, _, 16) => CIR.Lit(L.UInt16Lit(bv.toBigInt))
    case bv@BVLiteral(false, _, 32) => CIR.Lit(L.UInt32Lit(bv.toBigInt))
    case bv@BVLiteral(false, _, 64) => CIR.Lit(L.UInt64Lit(bv.toBigInt))

    case CharLiteral(v) => CIR.Lit(L.CharLit(v))
    case StringLiteral(v) => CIR.Lit(L.StringLit(v))

    case Block(es, last) => CIR.buildBlock((es :+ last) map rec)

    case v: Variable => buildBinding(v.toVal)

    case Let(x, e, body) if x.flags.contains(Ghost) => rec(body)
    case Let(x, e, body) => buildLet(x, e, body, isVar = false)
    case LetVar(x, e, body) => buildLet(x, e, body, isVar = true)

    case Assignment(v, expr) => CIR.Assign(buildBinding(v.toVal), rec(expr))

    case FieldAssignment(obj, fieldId0, expr) =>
      // The fieldId might actually not be the correct one;
      // it's global counter might differ from the one in the class definition.
      obj.getType match {
        case ct: ClassType =>
          val fields = ct.tcd.fields
          val optFieldId = fields collectFirst { case field if field.id.name == fieldId0.name => field.id }
          val fieldId = optFieldId getOrElse {
            reporter.fatalError(e.getPos, s"No corresponding field for $fieldId0 in class $ct")
          }
          CIR.Assign(CIR.FieldAccess(rec(obj), rec(fieldId, withUnique = !ct.tcd.cd.isExported)), rec(expr))

        case typ =>
          reporter.fatalError(e.getPos, s"Unexpected type $typ. Only class type are expected to update fields")
      }

    case LetRec(lfds, body) =>
      // We don't have to traverse the nested function now because we already have their contexts
      rec(body)((env._1, env._2 ++ lfds.map(lfd => lfd.id -> lfd)), tm0)

    case FunctionInvocation(id, tps, args) =>
      val fd = syms.getFunction(id)
      val tfd = fd.typed(tps)
      val fun = rec(Outer(fd), tps)
      implicit val tm1 = tm0 ++ tfd.tpSubst
      val nonGhostArgs = args.zip(fd.params).filter(!_._2.flags.contains(Ghost)).map(_._1)
      val args2 = nonGhostArgs map { a0 => rec(a0)(env, tm1) }
      CIR.App(fun.toVal, Seq(), args2)

    case ApplyLetRec(id, tparams, tpe, tps, args) =>
      val lfd = env._2(id)
      val fun = rec(Inner(lfd), tps)
      val tpSubst: TypeMapping = (lfd.tparams.map(_.tp) zip tps).toMap.filter(tt => tt._1 != tt._2)
      implicit val tm1 = tm0 ++ tpSubst
      val extra = ctxDB(lfd) map { c => convertVarInfoToParam(c)(tm1) }
      val nonGhostArgs = args.zip(lfd.params).filter(!_._2.flags.contains(Ghost)).map(_._1)
      val args2 = nonGhostArgs map { a0 => rec(a0)(env, tm1) }
      CIR.App(fun.toVal, extra, args2)

    case Application(fun0, args0) =>
      // Contrary to FunctionInvocation, Application of function-like object do not have to extend their
      // context as no environment variables are allowed to be captured.
      val fun = rec(fun0) match {
        case e if e.getType.isInstanceOf[CIR.FunType] => CIR.FunRef(e)
        case e => reporter.fatalError(fun0.getPos, s"Expected a binding but got $e of type ${e.getClass}.")
      }
      val args = args0 map rec

      CIR.App(fun, Nil, args)

    case Lambda(argsA, FunctionInvocation(id, tps, argsB))  =>
      val fd = syms.getFunction(id)
      val tfd = fd.typed(tps)
      // Lambda are okay for GenC iff they do not capture variables and call a function directly.
      // Additionally, the called function should not capture any environment variable.
      if ((argsA map { _.toVariable }) != argsB) {
        val strA = argsA.mkString("[", ", ", "]")
        val strB = argsB.mkString("[", ", ", "]")
        reporter.debug(s"This is a capturing lambda because: $strA != $strB")
        reporter.fatalError(e.getPos, s"Capturing lambda are not supported by GenC")
      }

      val fun = rec(Outer(fd), tps)

      if (fun.ctx.nonEmpty) {
        reporter.debug(s"${fun.id} is capturing some variables: ${fun.ctx mkString ", "}")
        reporter.fatalError(e.getPos, s"Function capturing their environment cannot be used as value")
      }

      fun.toVal

    case Lambda(args0, body0) =>
      reporter.debug(s"This is an unamed function; support is currently missing")
      reporter.debug(s"args = $args0, body = $body0 (${body0.getClass})")
      reporter.fatalError(e.getPos, s"Lambdas that don't directly invoke a function are not (yet) supported")

    case ClassConstructor(ct, args) =>
      val cd = syms.getClass(ct.id)
      val ct2 = rec(ct)
      val nonGhostArgs = args.zip(cd.fields).filter(!_._2.flags.contains(Ghost)).map(_._1)

      val args2 = nonGhostArgs map rec
      val positions = nonGhostArgs map { _.getPos }

      checkConstructArgs(args2 zip positions)

      CIR.Construct(ct2, args2)

    case ClassSelector(obj, fieldId) =>
      val cd = obj.getType.asInstanceOf[ClassType].tcd.cd
      CIR.FieldAccess(rec(obj), rec(fieldId, withUnique = !cd.isExported))

    case tuple @ Tuple(args0) =>
      val clazz = tuple2Class(tuple.getType)
      val args = args0 map rec
      val poss = args0 map { _.getPos }

      checkConstructArgs(args zip poss)

      CIR.Construct(clazz, args)

    case TupleSelect(tuple, idx) =>
      CIR.FieldAccess(rec(tuple), "_" + idx)

    case ArrayLength(array) => CIR.ArrayLength(rec(array))

    case ArraySelect(array, index) => CIR.ArrayAccess(rec(array), rec(index))

    case ArrayUpdated(array, index, newValue) => reporter.fatalError(e.getPos, s"Unsupported copy of array")

    case ArrayUpdate(array, index, value) =>
      CIR.Assign(CIR.ArrayAccess(rec(array), rec(index)), rec(value))

    case Swap(array1, index1, array2, index2) =>
      val ArrayType(base) = array1.getType
      val a1 = rec(array1)
      val a2 = rec(array2)
      val i1 = rec(index1)
      val i2 = rec(index2)
      val tmpId = rec(FreshIdentifier("tmp"))
      val tmpVd = CIR.ValDef(tmpId, rec(base), false)
      val tmp = CIR.Binding(tmpVd)
      CIR.buildBlock(Seq(
        CIR.DeclInit(tmpVd, CIR.ArrayAccess(a1, i1)),
        CIR.Assign(CIR.ArrayAccess(a1, i1), CIR.ArrayAccess(a2, i2)),
        CIR.Assign(CIR.ArrayAccess(a2, i2), tmp),
      ))

    case array @ FiniteArray(elems, base) =>
      val arrayType = CIR.ArrayType(rec(base), None)
      val length = elems.size
      CIR.ArrayInit(CIR.ArrayAllocStatic(arrayType, length, Right(elems.map(rec))))

    case array @ LargeArray(elems, default, size, base) =>
      val arrayType = CIR.ArrayType(rec(base), None)

      // Convert to VLA or normal array
      val alloc = rec(size) match {
        case CIR.Lit(L.Int32Lit(length)) =>
          // Optimisation for zero: don't generate values at all to speed up processing within GenC.
          val values = default match {
            case Int32Literal(0) | Int8Literal(0) => Left(CIR.Zero)
            case default => Right((0 until length.toInt) map { _ =>
              rec(exprOps.freshenLocals(default))
            })
          }
          CIR.ArrayAllocStatic(arrayType, length.toInt, values)

        case length =>
          if (arrayType.base.containsArray)
            reporter.fatalError(array.getPos, s"VLAs cannot have elements being/containing other array")

          reporter.warning(array.getPos, s"VLAs should be avoid according to MISRA C rules")

          val value = rec(default)
          CIR.ArrayAllocVLA(arrayType, length, value)
      }

      CIR.ArrayInit(alloc)

    case IfExpr(cond, thenn, NoTree(_)) => CIR.If(rec(cond), rec(thenn))
    case IfExpr(cond, thenn, elze) => CIR.IfElse(rec(cond), rec(thenn), rec(elze))

    case While(cond, body, _, _)     => CIR.While(rec(cond), rec(body))

    case LessThan(lhs, rhs)       => buildBinOp(lhs, O.LessThan, rhs)(e.getPos)
    case GreaterThan(lhs, rhs)    => buildBinOp(lhs, O.GreaterThan, rhs)(e.getPos)
    case LessEquals(lhs, rhs)     => buildBinOp(lhs, O.LessEquals, rhs)(e.getPos)
    case GreaterEquals(lhs, rhs)  => buildBinOp(lhs, O.GreaterEquals, rhs)(e.getPos)
    case Equals(lhs, rhs)         => buildBinOp(lhs, O.Equals, rhs)(e.getPos)
    case Not(Equals(lhs, rhs))    => buildBinOp(lhs, O.NotEquals, rhs)(e.getPos)

    case Not(rhs)                 => buildUnOp(O.Not, rhs)(e.getPos)
    case And(exprs)               => buildMultiOp(O.And, exprs)(e.getPos)
    case Or(exprs)                => buildMultiOp(O.Or, exprs)(e.getPos)

    case Plus(lhs, rhs)           => buildBinOp(lhs, O.Plus, rhs)(e.getPos)
    case Minus(lhs, rhs)          => buildBinOp(lhs, O.Minus, rhs)(e.getPos)
    case UMinus(rhs)              => buildUnOp(O.UMinus, rhs)(e.getPos)
    case Times(lhs, rhs)          => buildBinOp(lhs, O.Times, rhs)(e.getPos)
    case Division(lhs, rhs)       => buildBinOp(lhs, O.Div, rhs)(e.getPos)
    case Remainder(lhs, rhs)      => buildBinOp(lhs, O.Modulo, rhs)(e.getPos)
    case BVNot(rhs)               => buildUnOp(O.BNot, rhs)(e.getPos)
    case BVAnd(lhs, rhs)          => buildBinOp(lhs, O.BAnd, rhs)(e.getPos)
    case BVOr(lhs, rhs)           => buildBinOp(lhs, O.BOr, rhs)(e.getPos)
    case BVXor(lhs, rhs)          => buildBinOp(lhs, O.BXor, rhs)(e.getPos)
    case BVShiftLeft(lhs, rhs)    => buildBinOp(lhs, O.BLeftShift, rhs)(e.getPos)
    case BVAShiftRight(lhs, rhs)  => reporter.fatalError(e.getPos, "Operator >> is not supported by GenC")
    case BVLShiftRight(lhs, rhs)  => buildBinOp(lhs, O.BRightShift, rhs)(e.getPos)

    case BVWideningCast(e, t)  => CIR.IntegralCast(rec(e), rec(t).asInstanceOf[CIR.PrimitiveType].primitive.asInstanceOf[PT.IntegralPrimitiveType])
    case BVNarrowingCast(e, t) => CIR.IntegralCast(rec(e), rec(t).asInstanceOf[CIR.PrimitiveType].primitive.asInstanceOf[PT.IntegralPrimitiveType])

    case BVUnsignedToSigned(e) =>
      val BVType(false, size) = e.getType
      CIR.IntegralCast(rec(e), rec(BVType(true, size)).asInstanceOf[CIR.PrimitiveType].primitive.asInstanceOf[PT.IntegralPrimitiveType])
    case BVSignedToUnsigned(e) =>
      val BVType(true, size) = e.getType
      CIR.IntegralCast(rec(e), rec(BVType(false, size)).asInstanceOf[CIR.PrimitiveType].primitive.asInstanceOf[PT.IntegralPrimitiveType])

    case MatchExpr(scrutinee, cases) => convertPatMap(scrutinee, cases)

    case IsInstanceOf(expr, ct: ClassType) if castNotSupported(ct) =>
      reporter.fatalError(e.getPos, s"Membership tests on abstract classes are not supported by GenC")

    case IsInstanceOf(expr, ct: ClassType) => CIR.IsA(rec(expr), CIR.ClassType(rec(ct)))

    case AsInstanceOf(expr, ct: ClassType) if castNotSupported(ct) =>
      reporter.fatalError(e.getPos, s"Cast to abstract classes are not supported by GenC")

    case AsInstanceOf(expr, ct: ClassType) => CIR.AsA(rec(expr), CIR.ClassType(rec(ct)))

    case Return(expr) => CIR.Return(rec(expr))

    case e =>
      reporter.fatalError(e.getPos, s"Expression `${e.asString}` (${e.getClass}) not handled by GenC component")
  }

}

object Scala2IRPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[(Dependencies, FunCtxDB), CIR.Prog] = new {
    val context = ctx
  } with Scala2IRPhase
}
