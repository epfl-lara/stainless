/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.util.{Failure, Success, Try}

/** The annotations `FunctionRewrite` leaves for `AssignmentRewrite`: the results of calls, and the write backs of their effects. */
trait CallResults {
  val s: Trees
  import s._

  /** The part of a call result that a write back stores into an argument. */
  object CallResult {
    /** The annotation marking a call result. */
    val flag: Flag = Annotation("CallResult", Seq.empty)

    /** Whether `e` is a call result. */
    def unapply(e: Expr): Boolean = e match {
      case Annotated(_, flags) => flags.contains(flag)
      case _ => false
    }

    /** Whether `e` contains a call result. */
    def isWithin(e: Expr): Boolean =
      exprOps.exists { case CallResult() => true; case _ => false }(e)
  }

  /** An assignment that stores the effect of a call back into an argument, annotated with the location it writes. */
  object WriteBack {
    private val name = "WriteBack"

    /** The annotation marking a write back of `location`. */
    def flag(location: Expr): Flag = Annotation(name, Seq(location))

    /** The location of `flag`, when it marks a write back. */
    def location(flag: Flag): Option[Expr] = flag match {
      case Annotation(`name`, Seq(location: Expr @unchecked)) => Some(location)
      case _ => None
    }

    /** The location written by the assignment `e`, when it is a write back. */
    def unapply(e: Assignment): Option[Expr] = e.value match {
      case Annotated(_, flags) => flags.flatMap(location).headOption
      case _ => None
    }
  }
}

/** Makes the effects of calls explicit: each function returns its mutated parameters, and each call writes them back into its arguments. */
class FunctionRewrite(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with EffectsAnalyzer
     with GhostChecker
     with CallResults {
  import s._
  import exprOps._

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )
  override protected final val sortCache = new ExtractionCache[s.ADTSort, (SortResult, SortSummary)]((sort, context) =>
    getDependencyKey(sort.id)(using context.symbols)
  )
  override protected final val classCache = new ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]((cd, context) =>
    getDependencyKey(cd.id)(using context.symbols)
  )

  override protected type FunctionResult = Option[FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def getContext(symbols: Symbols) = TransformerContext()(using symbols)

  /** Whether a function was rewritten. */
  enum FunctionSummary {
    case Untransformed(fid: Identifier)
    case Transformed(fid: Identifier)
  }

  override protected def extractFunction(analysis: TransformerContext, fd: FunDef): (Option[FunDef], FunctionSummary) = {
    import analysis.{given, _}

    checkGhost(fd)(analysis)

    if (isMutableSynthetic(fd)) {
      return (None, FunctionSummary.Untransformed(fd.id))
    }

    ensureNoCapturedAssignments(fd.fullBody)

    val rewritten = rewriteFunction(Outer(fd), Map.empty, Set.empty)

    (Some(rewritten.toFun), FunctionSummary.Transformed(fd.id))
  }

  override protected type SortSummary = Unit
  override protected def extractSort(analysis: TransformerContext, sort: ADTSort): (ADTSort, Unit) =
    (analysis.transformer.transform(sort), ())

  override protected type ClassSummary = Unit
  override protected def extractClass(analysis: TransformerContext, cd: ClassDef): (ClassDef, Unit) =
    (analysis.transformer.transform(cd), ())

  override protected def combineSummaries(allSummaries: AllSummaries): ExtractionSummary = {
    val summary = allSummaries.fnsSummary.foldLeft(FunctionRewrite.SummaryData()) {
      case (summary, FunctionSummary.Untransformed(_)) => summary
      case (summary, FunctionSummary.Transformed(fid)) => summary.copy(affectedFns = summary.affectedFns + fid)
    }

    ExtractionSummary.Leaf(FunctionRewrite)(summary)
  }

  /** Rejects a local function or lambda that assigns a captured variable of mutable type. */
  private def ensureNoCapturedAssignments(body: Expr)(using symbols: Symbols): Unit = {
    def ensureLocalFunction(params: Seq[ValDef], localBody: Expr): Unit = {
      val captured = (exprOps.variablesOf(localBody) -- params.map(_.toVariable)).map(_.id)

      exprOps.preTraversal {
        case assignment @ Assignment(variable, _) if captured(variable.id) && symbols.isMutableType(variable.tpe) =>
          throw AliasingRewriteException.capturedMutation(assignment)

        case _ =>
      }(localBody)
    }

    exprOps.preTraversal {
      case LetRec(fds, _) => fds.foreach(fd => ensureLocalFunction(fd.params, fd.fullBody))
      case lambda: Lambda => ensureLocalFunction(lambda.params, lambda.body)
      case _ =>
    }(body)
  }

  /** The effects of the functions of `symbols`, and the rewriting that makes them explicit. */
  protected case class TransformerContext()(using override val symbols: Symbols) extends EffectsAnalysis {
    import symbols._

    /** `tpe` with a result that also returns the mutable parameters, when it has some. */
    def makeFunctionTypeExplicit(tpe: Type): Type = {
      def makeSigmaType(mutableParams: Seq[Type], returnType: Type): Type = {
        val freshParams = mutableParams.map(tpe => ValDef(FreshIdentifier("x"), tpe))

        sigmaTypeWrap(freshParams, returnType).copiedFrom(returnType)
      }

      tpe match {
        case ft @ FunctionType(from, to) =>
          val mutableParams = from.filter(isMutableType(_))

          if (mutableParams.isEmpty) {
            return ft
          }

          ft.copy(to = makeSigmaType(mutableParams, to)).copiedFrom(ft)

        case pt @ PiType(params, to) =>
          val mutableParamTypes = params.map(_.tpe).filter(isMutableType(_))

          if (mutableParamTypes.isEmpty) {
            return pt
          }

          pt.copy(to = makeSigmaType(mutableParamTypes, to)).copiedFrom(pt)
      }
    }

    /** Makes every function type explicit. */
    object transformer extends ConcreteOOSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case ApplyLetRec(id, tparams, tpe, tps, args) =>
          ApplyLetRec(
            id,
            tparams.map(tp => transform(tp).asInstanceOf[TypeParameter]),
            FunctionType(tpe.from.map(transform), transform(tpe.to)).copiedFrom(tpe),
            tps.map(transform),
            args.map(transform)
          ).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ft @ (_: FunctionType | _: PiType) => makeFunctionTypeExplicit(ft)
        case _ => super.transform(tpe)
      }
    }

    /** Whether `fd` is a synthetic function, other than an accessor, that takes mutable parameters and may return one of them. */
    def isMutableSynthetic(fd: FunDef): Boolean =
      fd.flags.contains(Synthetic) &&
        !fd.flags.exists(_.name == "accessor") &&
        fd.params.exists(vd => isMutableType(vd.tpe)) &&
        !exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.forall(isExpressionFresh)

    /** The local functions in scope, by name. */
    type Locals = Map[Identifier, LocalFunDef]

    /** `fd` returning its aliased parameters with its result, with its body and postcondition rewritten accordingly. */
    def rewriteFunction(fd: FunAbstraction, locals: Locals, outerWidenedVarIds: Set[Identifier]): FunAbstraction = {
      def desugarSwaps(body: Expr): Expr = {
        def isPath(e: Expr): Boolean = e match {
          case _: Variable => true
          case ClassSelector(owner, _) => isPath(owner)
          case ADTSelector(owner, _) => isPath(owner)
          case TupleSelect(owner, _) => isPath(owner)
          case AsInstanceOf(owner, _) => isPath(owner)
          case Annotated(owner, _) => isPath(owner)
          case ArraySelect(owner, index) if symbols.isImmutableExpression(index) => isPath(owner)
          case MutableMapApply(owner, key) if symbols.isImmutableExpression(key) => isPath(owner)
          case _ => false
        }

        def bind(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
          val vd = ValDef.fresh(name, e.getType).copiedFrom(e)

          (Seq(vd -> e), vd.toVariable)
        }

        def bindUnlessPath(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
          if (isPath(e)) {
            return (Seq.empty, e)
          }

          bind(e, name)
        }

        def bindUnlessImmutable(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isImmutableExpression(e)) {
            return (Seq.empty, e)
          }

          bind(e, name)
        }

        def withBindings(bindings: Seq[(ValDef, Expr)], body: Expr): Expr =
          bindings.foldRight(body) { case ((vd, value), rest) => Let(vd, value, rest).copiedFrom(body) }

        exprOps.postMap {
          case swap @ Swap(array1, index1, array2, index2) =>
            val (receiverBindings1, receiver1) = bindUnlessPath(array1, "array")
            val (receiverBindings2, receiver2) = bindUnlessPath(array2, "array")
            val (indexBindings1, i1) = bindUnlessImmutable(index1, "i1")
            val (indexBindings2, i2) = bindUnlessImmutable(index2, "i2")
            val ArrayType(base) = array1.getType: @unchecked
            val temp = ValDef.fresh("temp", base).copiedFrom(swap)
            val first = ArrayUpdate(receiver1, i1, ArraySelect(receiver2, i2).copiedFrom(swap)).copiedFrom(swap)
            val second = ArrayUpdate(receiver2, i2, temp.toVariable).copiedFrom(swap)
            val exchange = Let(temp, ArraySelect(receiver1, i1).copiedFrom(swap), Block(Seq(first), second).copiedFrom(swap)).copiedFrom(swap)
            val bindings = receiverBindings1 ++ indexBindings1 ++ receiverBindings2 ++ indexBindings2

            Some(withBindings(bindings, exchange))

          case cellSwap @ CellSwap(cell1, cell2) =>
            val field = symbols.lookup.get[ClassDef]("stainless.lang.Cell").get.fields.head.id
            val (bindings1, receiver1) = bindUnlessPath(cell1, "cell")
            val (bindings2, receiver2) = bindUnlessPath(cell2, "cell")
            val cellType @ ClassType(_, _) = cell1.getType: @unchecked
            val temp = ValDef.fresh("temp", getClassField(cellType, field).get.tpe).copiedFrom(cellSwap)
            val first = FieldAssignment(receiver1, field, ClassSelector(receiver2, field).copiedFrom(cellSwap)).copiedFrom(cellSwap)
            val second = FieldAssignment(receiver2, field, temp.toVariable).copiedFrom(cellSwap)
            val exchange = Let(temp, ClassSelector(receiver1, field).copiedFrom(cellSwap), Block(Seq(first), second).copiedFrom(cellSwap)).copiedFrom(cellSwap)

            Some(withBindings(bindings1 ++ bindings2, exchange))

          case _ =>
            None
        }(body)
      }

      val widenings = fd.params.flatMap(widenBinder)
      val widenedParams = widenings.map { case (newVd, _) => newVd.id -> newVd }.toMap
      val newParams = fd.params.map(vd => widenedParams.getOrElse(vd.id, vd))
      val newFd = fd.copy(params = newParams, returnType = transformer.transform(getReturnType(fd)))
      val widenedVarIds = outerWidenedVarIds ++ widenedParams.keySet
      val paramSubstitution: Map[Variable, Expr] = widenings.map(_._2).toMap
      val widenedFullBody = desugarSwaps(exprOps.replaceFromSymbols(paramSubstitution, fd.fullBody))

      val aliasedParams = getAliasedParams(fd)

      if (aliasedParams.isEmpty) {
        return newFd.copy(fullBody = rewriteBody(widenedFullBody, Seq.empty, locals, widenedVarIds))
      }

      val (specs, body) = exprOps.deconstructSpecs(widenedFullBody)
      val (copies, copySubstitution) = copiesOf(aliasedParams)

      val newBody = body.map { body =>
        val substitutedBody = exprOps.replaceFromSymbols(copySubstitution, body)
        val rewritten = rewriteBody(substitutedBody, copies.map(_.toVariable), locals, widenedVarIds)
        val resultType = typeOps.replaceFromSymbols(copySubstitution, transformer.transform(fd.returnType))

        withReturnedCopies(aliasedParams, copies, rewritten, resultType, body)
      }

      val newSpecs = specs.map {
        case exprOps.Postcondition(post @ Lambda(Seq(res), postBody)) =>
          val newRes = ValDef(res.id.freshen, newFd.returnType).copiedFrom(res)
          val oldSubstitution: Map[Expr, Expr] = aliasedParams.map(vd => Old(vd.toVariable) -> vd.toVariable).toMap
          val copySelections: Map[Expr, Expr] = aliasedParams.zipWithIndex
            .map { case (vd, i) => vd.toVariable -> TupleSelect(newRes.toVariable, i + 1).copiedFrom(vd) }
            .toMap
          val resultSelection: (Expr, Expr) = res.toVariable -> TupleSelect(newRes.toVariable, aliasedParams.length + 1).copiedFrom(res)
          val rewrittenPost = rewriteBody(postBody, Seq.empty, locals, widenedVarIds)
          val newPostBody = exprOps.replaceSingle(oldSubstitution ++ copySelections + resultSelection, rewrittenPost)

          exprOps.Postcondition(Lambda(Seq(newRes), newPostBody).copiedFrom(post))

        case spec =>
          spec
      }

      newFd.copy(fullBody = exprOps.reconstructSpecs(newSpecs, newBody, newFd.returnType))
    }

    /** `body` with its calls writing back their effects, and its returns returning `returnedCopies` too. */
    private def rewriteBody(body: Expr, returnedCopies: Seq[Variable], locals: Locals, widenedVarIds: Set[Identifier]): Expr = {
      def widenPatternBinders(pattern: Pattern): (Pattern, Map[Variable, Expr]) = {
        val (ids, binders, exprs, tps, subPatterns, builder) = deconstructor.deconstruct(pattern)

        val widenedBinders = binders.map(binder => widenBinder(binder.toVal))
        val newBinders = binders.zip(widenedBinders).map { case (binder, widened) => widened.fold(binder)(_._1.toVariable) }
        val binderSubstitution: Map[Variable, Expr] = widenedBinders.flatten.map(_._2).toMap

        val widenedSubPatterns = subPatterns.map(widenPatternBinders)
        val substitution = widenedSubPatterns.foldLeft(binderSubstitution)(_ ++ _._2)

        (builder(ids, newBinders, exprs, tps, widenedSubPatterns.map(_._1)).copiedFrom(pattern), substitution)
      }

      def resolveResultType(e: Expr): Type = e match {
        case Let(_, _, body) => resolveResultType(body)
        case LetVar(_, _, body) => resolveResultType(body)
        case Block(_, last) => resolveResultType(last)
        case _ => e.getType
      }

      object transformer extends ConcreteOOSelfTreeTransformer {
        def rewriteBinding(vd: ValDef, value: Expr, body: Expr)(rebuild: (ValDef, Expr, Expr) => Expr): Expr = widenBinder(vd) match {
          case None =>
            rebuild(vd, transform(value), transform(body))

          case Some((newVd, substitution)) =>
            val substitutedBody = exprOps.replaceFromSymbols(Map(substitution), body)

            rebuild(newVd, transform(value), rewriteBody(substitutedBody, returnedCopies, locals, widenedVarIds + vd.id))
        }

        def rewriteCase(matchCase: MatchCase): MatchCase = {
          val (newPattern, substitution) = widenPatternBinders(matchCase.pattern)

          if (substitution.isEmpty) {
            return MatchCase(matchCase.pattern, matchCase.optGuard.map(transform), transform(matchCase.rhs)).copiedFrom(matchCase)
          }

          val newWidenedIds = widenedVarIds ++ substitution.keys.map(_.id)
          val substitutedGuard = matchCase.optGuard.map(guard => exprOps.replaceFromSymbols(substitution, guard))
          val substitutedRhs = exprOps.replaceFromSymbols(substitution, matchCase.rhs)

          MatchCase(
            newPattern,
            substitutedGuard.map(guard => rewriteBody(guard, returnedCopies, locals, newWidenedIds)),
            rewriteBody(substitutedRhs, returnedCopies, locals, newWidenedIds)
          ).copiedFrom(matchCase)
        }

        override def transform(e: Expr): Expr = e match {
          case Return(_) if returnedCopies.isEmpty =>
            super.transform(e)

          case ret @ Return(retExpr) =>
            Return(Tuple(returnedCopies.map(_.copy().copiedFrom(ret)) :+ transform(retExpr)).setPos(ret)).setPos(ret)

          case l @ LetRec(fds, letBody) =>
            val newLocals = locals ++ fds.map(f => f.id -> f)
            val nfds = fds.map(fd => rewriteFunction(Inner(fd), newLocals, widenedVarIds).toLocal)

            LetRec(nfds, rewriteBody(letBody, returnedCopies, newLocals, widenedVarIds)).copiedFrom(l)

          case ens @ Ensuring(ensBody, pred @ Lambda(Seq(resVd), predBody)) =>
            Ensuring(transform(ensBody), Lambda(Seq(resVd), transform(predBody)).copiedFrom(pred)).copiedFrom(ens)

          case l @ Let(vd, value, letBody) =>
            rewriteBinding(vd, value, letBody)((vd, value, body) => Let(vd, value, body).copiedFrom(l))

          case l @ LetVar(vd, value, letBody) =>
            rewriteBinding(vd, value, letBody)((vd, value, body) => LetVar(vd, value, body).copiedFrom(l))

          case m @ MatchExpr(scrutinee, cases) =>
            MatchExpr(transform(scrutinee), cases.map(rewriteCase)).copiedFrom(m)

          case l @ Lambda(params, lambdaBody) =>
            val aliasedParams = params.filter(vd => isMutableType(vd.tpe))

            if (aliasedParams.isEmpty) {
              return Lambda(params, transform(lambdaBody)).copiedFrom(l)
            }

            val (copies, substitution) = copiesOf(aliasedParams)
            val substitutedBody = exprOps.replaceFromSymbols(substitution, lambdaBody)
            val rewritten = rewriteBody(substitutedBody, returnedCopies, locals, widenedVarIds)
            val resultType = resolveResultType(rewritten)

            Lambda(params, withReturnedCopies(aliasedParams, copies, rewritten, resultType, lambdaBody)).copiedFrom(l)

          case FunctionInvocation(unfoldId @ ast.SymbolIdentifier("stainless.lang.unfold"), Seq(_), Seq(fi: FunctionInvocation)) =>
            val callee = Outer(fi.tfd.fd)
            val instantiatedType = fi.tfd.instantiate(getReturnType(callee))

            withBoundArguments(fi.args, fi.args.map(transform)) { (targets, boundArgs) =>
              val call = FunctionInvocation(fi.id, fi.tps, boundArgs).copiedFrom(fi)
              val resultType = typeOps.replaceFromSymbols(callee.params.zip(boundArgs).toMap, instantiatedType)
              val rewrittenCall = rewriteCallEffects(callee.params, targets, call, resultType, effects(callee), selectResult = false)

              FunctionInvocation(unfoldId, Seq(resultType), Seq(rewrittenCall)).copiedFrom(fi)
            }

          case fi: FunctionInvocation =>
            val callee = Outer(fi.tfd.fd)
            val instantiatedType = fi.tfd.instantiate(getReturnType(callee))

            withBoundArguments(fi.args, fi.args.map(transform)) { (targets, boundArgs) =>
              val call = FunctionInvocation(fi.id, fi.tps, boundArgs).copiedFrom(fi)
              val resultType = typeOps.replaceFromSymbols(callee.params.zip(boundArgs).toMap, instantiatedType)

              rewriteCallEffects(callee.params, targets, call, resultType, effects(callee), selectResult = true)
            }

          case application @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val callee = Inner(locals(id))
            val calleeType = FunctionType(callee.params.map(_.getType), getReturnType(callee)).copiedFrom(tpe)
            val instantiatedType = typeOps.instantiateType(getReturnType(callee), tparams.zip(tps).toMap)

            withBoundArguments(args, args.map(transform)) { (targets, boundArgs) =>
              val call = ApplyLetRec(id, tparams, calleeType, tps, boundArgs).copiedFrom(application)
              val resultType = typeOps.replaceFromSymbols(callee.params.zip(boundArgs).toMap, instantiatedType)

              rewriteCallEffects(callee.params, targets, call, resultType, effects(callee), selectResult = true)
            }

          case application @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType: @unchecked
            val transformedCallee = transform(callee)
            val calleeEffects = functionTypeEffects(ft)

            def rewriteApplication(targets: Seq[Expr], boundArgs: Seq[Expr]): Expr = {
              val call = Application(transformedCallee, boundArgs).copiedFrom(application)

              if (calleeEffects.isEmpty) {
                return call
              }

              val params = from.map(tpe => ValDef.fresh("x", tpe))
              val paramEffects = params.zipWithIndex.collect {
                case (vd, index) if calleeEffects(index) => ModifyingEffect(vd.toVariable, Path.empty)
              }
              val resultType = callee match {
                case v: Variable if widenedVarIds(v.id) => to
                case _ => makeFunctionTypeExplicit(ft).asInstanceOf[FunctionType].to
              }

              rewriteCallEffects(params, targets, call, resultType, paramEffects.toSet, selectResult = true)
            }

            if (exprOps.hasEffect(transformedCallee)) {
              return rewriteApplication(args, args.map(transform))
            }

            withBoundArguments(args, args.map(transform))(rewriteApplication)

          case _ =>
            super.transform(e)
        }
      }

      transformer.transform(body)
    }

    /** The statements and bindings `e` starts with, as a context for what follows them, and the expression they lead to. */
    private def splitPrefix(e: Expr): (Expr => Expr, Expr) = e match {
      case Block(statements, last) =>
        val (prefix, result) = splitPrefix(last)
        (rest => Block(statements, prefix(rest)).copiedFrom(e), result)

      case Let(vd, value, body) =>
        val (prefix, result) = splitPrefix(body)
        (rest => Let(vd, value, prefix(rest)).copiedFrom(e), result)

      case LetVar(vd, value, body) =>
        val (prefix, result) = splitPrefix(body)
        (rest => LetVar(vd, value, prefix(rest)).copiedFrom(e), result)

      case _ =>
        (identity, e)
    }

    /** `rebuild` applied to the effect targets and the arguments of a call, each argument bound to a fresh variable in order when one of them has an effect. */
    private def withBoundArguments(args: Seq[Expr], transformedArgs: Seq[Expr])(rebuild: (Seq[Expr], Seq[Expr]) => Expr): Expr = {
      if (!transformedArgs.exists(exprOps.hasEffect)) {
        return rebuild(args, transformedArgs)
      }

      val bindings = transformedArgs.map { arg =>
        val (prefix, value) = splitPrefix(arg)

        (prefix, ValDef.fresh("arg", value.getType).copiedFrom(arg), value)
      }
      val variables = bindings.map { case (_, vd, _) => vd.toVariable }

      bindings.foldRight(rebuild(variables, variables)) { case ((prefix, vd, value), rest) =>
        val binding = if (isMutableType(value.getType)) LetVar(vd, value, rest) else Let(vd, value, rest)

        prefix(binding.copiedFrom(value))
      }
    }

    /** `call` followed by the write backs of the effects it has on `args`, resulting in its own result when `selectResult`. */
    private def rewriteCallEffects(
      formalParams: Seq[ValDef],
      args: Seq[Expr],
      call: Expr,
      resultType: Type,
      calleeEffects: Set[Effect],
      selectResult: Boolean
    ): Expr = {
      val mutatedArgs = formalParams.zip(args)
        .map { case (vd, arg) => (vd.toVariable, calleeEffects.filter(_.receiver == vd.toVariable), arg) }
        .filter { case (_, effects, _) => effects.nonEmpty }

      if (mutatedArgs.isEmpty) {
        return call
      }

      val result = ValDef(FreshIdentifier("res"), resultType).copiedFrom(call)

      val assignments = mutatedArgs.zipWithIndex.flatMap { case ((param, effects, arg), effectIndex) =>
        val argumentResult = TupleSelect(result.toVariable, effectIndex + 1)

        Try(ModifyingEffect(param, Path.empty).on(arg)) match {
          case Success(wholeTargets) =>
            wholeTargets.toSeq.map { case (effect, effectCondition) =>
              writeBackAssignment(arg.getPos, argumentResult, Seq.empty, effect.toTarget(effectCondition))
            }

          case Failure(_) =>
            effects.toSeq.flatMap { calleeEffect =>
              (calleeEffect `on` arg).toSeq.map { case (argumentEffect, effectCondition) =>
                val knownCalleeEffect = calleeEffect.removeUnknownAccessor
                val knownArgumentEffect = argumentEffect.removeUnknownAccessor

                writeBackAssignment(arg.getPos, argumentResult, knownCalleeEffect.path.path, knownArgumentEffect.toTarget(effectCondition))
              }
            }
        }
      }

      val resultExpr =
        if (selectResult) TupleSelect(result.toVariable, mutatedArgs.length + 1)
        else result.toVariable

      Let(result, call, Block(assignments, resultExpr))
    }

    /** The assignment that writes back into `target` the part of `argumentResult` reached through `outerPath`. */
    private def writeBackAssignment(pos: inox.utils.Position, argumentResult: Expr, outerPath: Seq[Accessor], target: Target): Expr = {
      def select(tpe: Type, expr: Expr, path: Seq[Accessor]): (Expr, Expr) = (tpe, path) match {
        case (adt: ADTType, ADTFieldAccessor(id) +: rest) =>
          val constructors = adt.getSort.constructors
          val constructor = constructors.find(_.fields.exists(_.id == id)).get
          val field = constructor.fields.find(_.id == id).get

          val condition = if (constructors.size > 1) IsConstructor(expr, constructor.id).setPos(pos) else BooleanLiteral(true).setPos(pos)
          val (restCondition, restSelect) = select(field.tpe, ADTSelector(expr, id).setPos(pos), rest)

          (and(condition, restCondition), restSelect)

        case (ct: ClassType, ClassFieldAccessor(selector) +: rest) =>
          val field = getClassField(ct, selector.id).get
          val fieldClassType = classForField(ct, selector.id).get.toType
          val isFinal = ct.tcd.cd.parents.isEmpty && ct.tcd.cd.children.isEmpty
          val condition = if (isFinal) BooleanLiteral(true).setPos(pos) else IsInstanceOf(expr, fieldClassType).setPos(pos)
          val casted = if (isFinal) expr else AsInstanceOf(expr, fieldClassType).setPos(expr)

          val (restCondition, restSelect) = select(field.tpe, ClassSelector(casted, selector.id).setPos(pos), rest)

          (and(condition, restCondition), restSelect)

        case (tt: TupleType, TupleFieldAccessor(index) +: rest) =>
          select(tt.bases(index - 1), TupleSelect(expr, index).setPos(pos), rest)

        case (ArrayType(base), ArrayAccessor(index) +: rest) =>
          select(base, ArraySelect(expr, index).setPos(pos), rest)

        case (MutableMapType(from, to), MutableMapAccessor(index) +: rest) =>
          select(to, MutableMapApply(expr, index).setPos(pos), rest)

        case (_, Nil) => (BooleanLiteral(true).setPos(pos), expr)

        case (_, _) => throw AliasingRewriteException.unrebuildableValue(expr)
      }

      def updatedTarget(target: Target, newValue: Expr): Expr = {
        def updatedPath(receiver: Expr, path: Seq[Accessor]): Expr = path match {
          case ADTFieldAccessor(id) :: rest =>
            val adt @ ADTType(_, tps) = receiver.getType: @unchecked
            val constructor = adt.getSort.constructors.find(_.fields.exists(_.id == id)).get
            val updatedField = updatedPath(Annotated(ADTSelector(receiver, id).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), rest)

            ADT(constructor.id, tps, constructor.definition.fields.map { vd =>
              if (vd.id == id) freshenLocals(updatedField)
              else freshenLocals(Annotated(ADTSelector(receiver, vd.id).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
            }).copiedFrom(newValue)

          case ClassFieldAccessor(selector) :: rest =>
            val cd = receiver.getType match {
              case ct: ClassType => classForField(ct, selector.id).getOrElse(throw AliasingRewriteException.unknownFieldOwner(receiver))
              case _ => throw AliasingRewriteException.unrebuildableValue(receiver)
            }
            val ct = cd.toType
            val isFinal = cd.parents.isEmpty && cd.children.isEmpty

            val casted = if (isFinal) receiver else AsInstanceOf(receiver, ct).copiedFrom(receiver)
            val updatedField =
              if (isFinal) updatedPath(ClassSelector(casted, selector.id), rest)
              else updatedPath(Annotated(ClassSelector(casted, selector.id).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), rest)

            ClassConstructor(ct, ct.tcd.fields.map { vd =>
              if (vd.id == selector.id) freshenLocals(updatedField)
              else if (isFinal) ClassSelector(freshenLocals(casted), vd.id)
              else freshenLocals(Annotated(ClassSelector(casted, vd.id).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
            }).copiedFrom(newValue)

          case TupleFieldAccessor(index) :: rest =>
            val tt @ TupleType(_) = receiver.getType: @unchecked
            val updatedField = updatedPath(Annotated(TupleSelect(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), rest)

            Tuple((1 to tt.dimension).map { position =>
              if (position == index) freshenLocals(updatedField)
              else freshenLocals(Annotated(TupleSelect(receiver, position).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
            }).copiedFrom(newValue)

          case ArrayAccessor(index) :: rest =>
            val updatedElement = freshenLocals(updatedPath(Annotated(ArraySelect(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), rest))

            freshenLocals(ArrayUpdated(receiver, index, updatedElement).copiedFrom(newValue))

          case MutableMapAccessor(index) :: rest =>
            val updatedElement = freshenLocals(updatedPath(Annotated(MutableMapApply(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), rest))

            freshenLocals(MutableMapUpdated(receiver, freshenLocals(index), updatedElement).copiedFrom(newValue))

          case Nil =>
            newValue
        }

        target match {
          case Target(receiver, None | Some(BooleanLiteral(true)), path) =>
            updatedPath(receiver, path.toSeq)

          case Target(_, Some(condition), _) if effects(condition).nonEmpty =>
            throw MalformedStainlessCode(condition, s"Effects are not allowed in condition of effects: ${condition.asString}")

          case Target(receiver, Some(condition), path) =>
            val updatedReceiver = updatedPath(receiver, path.toSeq)

            Annotated(
              AsInstanceOf(
                IfExpr(
                  condition.setPos(newValue),
                  Annotated(updatedReceiver, Seq(DropVCs)).copiedFrom(updatedReceiver),
                  receiver
                ).copiedFrom(newValue),
                receiver.getType
              ).copiedFrom(newValue),
              Seq(DropVCs)
            ).copiedFrom(newValue)
        }
      }

      def writtenLocation(path: Seq[Accessor]): Expr = Path(path).wrap(target.receiver) match {
        case Some(location) if path.isEmpty || isMutableType(location.getType) => location
        case _ => writtenLocation(path.init)
      }

      val (condition, result) = select(argumentResult.getType, argumentResult, outerPath)
      val combinedCondition = andJoin(condition +: target.condition.toSeq)

      if (combinedCondition == BooleanLiteral(false) || !isMutableType(target.receiver.getType)) {
        return UnitLiteral().setPos(pos)
      }

      val callResult = Annotated(result, Seq(DropVCs, CallResult.flag)).copiedFrom(result)
      val newValue = updatedTarget(target.copy(condition = Some(combinedCondition)), callResult)
      val castedValue = target.receiver.getType match {
        case adt: ADTType if adt.getSort.constructors.size == 1 => newValue
        case receiverType =>
          val casted = AsInstanceOf(newValue, receiverType).copiedFrom(newValue)

          Annotated(casted, Seq(DropVCs)).copiedFrom(casted)
      }

      val location = writtenLocation(target.path.toSeq)

      Assignment(target.receiver, Annotated(castedValue, Seq(WriteBack.flag(location))).copiedFrom(castedValue)).setPos(pos)
    }

    /** `vd` with its function types made explicit, and the substitution of the old variable, when its type changes. */
    private def widenBinder(vd: ValDef): Option[(ValDef, (Variable, Expr))] = {
      val widenedTpe = transformer.transform(vd.tpe)

      if (widenedTpe == vd.tpe) {
        return None
      }

      val newVd = vd.copy(tpe = widenedTpe).copiedFrom(vd)

      Some((newVd, (vd.toVariable, newVd.toVariable)))
    }

    /** A fresh copy of each of `aliasedParams`, and the substitution of each parameter by its copy. */
    private def copiesOf(aliasedParams: Seq[ValDef]): (Seq[ValDef], Map[Variable, Expr]) = {
      val copies = aliasedParams.map(_.freshen)
      val substitution: Map[Variable, Expr] = aliasedParams
        .zip(copies)
        .map { case (param, copy) => param.toVariable -> copy.toVariable }
        .toMap

      (copies, substitution)
    }

    /** `body`, run on copies of `params` initialized from them, returning the copies with its result. */
    private def withReturnedCopies(params: Seq[ValDef], copies: Seq[ValDef], body: Expr, resultType: Type, pos: Expr): Expr = {
      val res = ValDef(FreshIdentifier("res"), resultType)
      val returned: Expr = Let(res, body, Tuple(copies.map(_.toVariable) :+ res.toVariable).copiedFrom(pos)).copiedFrom(pos)

      copies.zip(params).foldLeft(returned) { case (rest, (copy, param)) =>
        LetVar(copy, param.toVariable, rest).copiedFrom(pos)
      }
    }
  }
}

object FunctionRewrite extends ExtractionPipelineCreator {
  /** The functions the phase rewrote. */
  case class SummaryData(affectedFns: Set[Identifier] = Set.empty) {
    /** The functions either summary rewrote. */
    def ++(other: SummaryData): SummaryData = SummaryData(affectedFns ++ other.affectedFns)

    /** Whether the phase rewrote a function. */
    def hasRun: Boolean = affectedFns.nonEmpty
  }

  override val name: String = "FunctionRewrite"

  /** The phase over the trees `trees`. */
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends FunctionRewrite(s)(t)

    new Impl(trees, trees)
  }
}
