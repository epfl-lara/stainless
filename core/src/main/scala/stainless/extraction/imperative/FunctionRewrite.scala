/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import scala.util.{Failure, Success, Try}

trait CallResults {
  val s: Trees
  import s._

  object CallResult {
    val flag: Flag = Annotation("CallResult", Seq.empty)

    def unapply(e: Expr): Boolean = e match {
      case Annotated(_, flags) => flags.contains(flag)
      case _ => false
    }

    def isWithin(e: Expr): Boolean =
      exprOps.exists { case CallResult() => true; case _ => false }(e)
  }

  object WriteBack {
    private val name = "WriteBack"

    def flag(location: Expr): Flag = Annotation(name, Seq(location))

    def location(flag: Flag): Option[Expr] = flag match {
      case Annotation(`name`, Seq(location: Expr @unchecked)) => Some(location)
      case _ => None
    }

    def unapply(e: Assignment): Option[Expr] = e.value match {
      case Annotated(_, flags) => flags.flatMap(location).headOption
      case _ => None
    }
  }
}

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

    ensureInstantiations(fd)
    ensureNoCapturedAssignments(fd.fullBody)

    val rewritten = rewriteFunction(Outer(fd), Map.empty, Set.empty)

    (Some(rewritten.toFun), FunctionSummary.Transformed(fd.id))
  }

  override protected type SortSummary = Unit
  override protected def extractSort(analysis: TransformerContext, sort: ADTSort): (ADTSort, Unit) =
    (analysis.transformer.transform(sort), ())

  override protected type ClassSummary = Unit
  override protected def extractClass(analysis: TransformerContext, cd: ClassDef): (ClassDef, Unit) = {
    import analysis.given

    val instantiations = InstantiationTraverser()
    cd.fields.foreach(field => instantiations.traverse(field.tpe))

    (analysis.transformer.transform(cd), ())
  }

  override protected def combineSummaries(allSummaries: AllSummaries): ExtractionSummary = {
    val summary = allSummaries.fnsSummary.foldLeft(FunctionRewrite.SummaryData()) {
      case (summary, FunctionSummary.Untransformed(_)) => summary
      case (summary, FunctionSummary.Transformed(fid)) => summary.copy(affectedFns = summary.affectedFns + fid)
    }
    ExtractionSummary.Leaf(FunctionRewrite)(summary)
  }

  private def ensureInstantiations(fd: FunDef)(using Symbols): Unit = {
    val instantiations = InstantiationTraverser()
    instantiations.traverse(fd.fullBody)
    fd.params.foreach(param => instantiations.traverse(param.tpe))
  }

  private class InstantiationTraverser(using symbols: Symbols) extends ConcreteSelfTreeTraverser {
    import symbols.isMutableType

    private def ensureTypeArguments(tree: Tree, tparams: Seq[TypeParameterDef], tps: Seq[Type]): Unit = {
      tparams.zip(tps).foreach { case (tdef, instance) =>
        if (isMutableType(instance) && !tdef.flags.contains(IsMutable)) {
          throw AliasingRewriteException.mutableInstantiation(tree)
        }
      }
    }

    override def traverse(tpe: Type): Unit = {
      tpe match {
        case ct: ClassType => ensureTypeArguments(tpe, ct.tcd.cd.tparams, ct.tps)
        case adt: ADTType => ensureTypeArguments(tpe, adt.getSort.definition.tparams, adt.tps)
        case SetType(element) if isMutableType(element) => throw AliasingRewriteException.mutableInstantiation(tpe)
        case BagType(element) if isMutableType(element) => throw AliasingRewriteException.mutableInstantiation(tpe)
        case MapType(from, _) if isMutableType(from) => throw AliasingRewriteException.mutableInstantiation(tpe)
        case MutableMapType(from, _) if isMutableType(from) => throw AliasingRewriteException.mutableInstantiation(tpe)
        case _ =>
      }

      super.traverse(tpe)
    }

    override def traverse(e: Expr): Unit = {
      e match {
        case fi: FunctionInvocation => ensureTypeArguments(fi, fi.tfd.fd.tparams, fi.tps)
        case adt: ADT => ensureTypeArguments(adt, adt.getConstructor.sort.definition.tparams, adt.tps)
        case _ =>
      }

      super.traverse(e)
    }
  }

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

  protected case class TransformerContext()(using override val symbols: Symbols) extends EffectsAnalysis {
    import symbols._

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

    object transformer extends ConcreteOOSelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case ApplyLetRec(id, tparams, tpe, tps, args) =>
          ApplyLetRec(
            id,
            tparams map (tp => transform(tp).asInstanceOf[TypeParameter]),
            FunctionType(tpe.from map transform, transform(tpe.to)).copiedFrom(tpe),
            tps map transform,
            args map transform
          ).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ft @ (_: FunctionType | _: PiType) => makeFunctionTypeExplicit(ft)
        case _ => super.transform(tpe)
      }
    }

    def isMutableSynthetic(fd: FunDef): Boolean =
      fd.flags.contains(Synthetic) &&
        !fd.flags.exists(_.name == "accessor") &&
        fd.params.exists(vd => isMutableType(vd.tpe)) &&
        !exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.forall(isExpressionFresh)

    type Locals = Map[Identifier, LocalFunDef]

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

        def bindReceiver(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
          if (isPath(e)) {
            return (Seq.empty, e)
          }

          bind(e, name)
        }

        def bindIndex(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
          if (symbols.isImmutableExpression(e)) {
            return (Seq.empty, e)
          }

          bind(e, name)
        }

        def withBindings(bindings: Seq[(ValDef, Expr)], e: Expr): Expr =
          bindings.foldRight(e) { case ((vd, value), rest) => Let(vd, value, rest).copiedFrom(e) }

        exprOps.postMap {
          case swap @ Swap(array1, index1, array2, index2) =>
            val ArrayType(base) = array1.getType: @unchecked
            val (receiverBindings1, receiver1) = bindReceiver(array1, "array")
            val (receiverBindings2, receiver2) = bindReceiver(array2, "array")
            val (indexBindings1, i1) = bindIndex(index1, "i1")
            val (indexBindings2, i2) = bindIndex(index2, "i2")
            val temp = ValDef.fresh("temp", base).copiedFrom(swap)
            val first = ArrayUpdate(receiver1, i1, ArraySelect(receiver2, i2).copiedFrom(swap)).copiedFrom(swap)
            val second = ArrayUpdate(receiver2, i2, temp.toVariable).copiedFrom(swap)
            val exchange = Let(temp, ArraySelect(receiver1, i1).copiedFrom(swap), Block(Seq(first), second).copiedFrom(swap)).copiedFrom(swap)
            val bindings = receiverBindings1 ++ indexBindings1 ++ receiverBindings2 ++ indexBindings2

            Some(withBindings(bindings, exchange))

          case cellSwap @ CellSwap(cell1, cell2) =>
            val cellType @ ClassType(_, _) = cell1.getType: @unchecked
            val field = symbols.lookup.get[ClassDef]("stainless.lang.Cell").get.fields.head.id
            val (bindings1, receiver1) = bindReceiver(cell1, "cell")
            val (bindings2, receiver2) = bindReceiver(cell2, "cell")
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
          val copySelections: Map[Expr, Expr] = aliasedParams.zipWithIndex.map { case (vd, i) =>
            vd.toVariable -> TupleSelect(newRes.toVariable, i + 1).copiedFrom(vd)
          }.toMap
          val resultSelection: (Expr, Expr) = res.toVariable -> TupleSelect(newRes.toVariable, aliasedParams.length + 1).copiedFrom(res)
          val rewrittenPost = rewriteBody(postBody, Seq.empty, locals, widenedVarIds)
          val newPostBody = exprOps.replaceSingle(oldSubstitution ++ copySelections + resultSelection, rewrittenPost)

          exprOps.Postcondition(Lambda(Seq(newRes), newPostBody).copiedFrom(post))

        case spec => spec
      }

      newFd.copy(fullBody = exprOps.reconstructSpecs(newSpecs, newBody, newFd.returnType))
    }

    private def rewriteBody(body: Expr, freshLocals: Seq[Variable], locals: Locals, widenedVarIds: Set[Identifier]): Expr = {
      def widenPatternBinders(pattern: Pattern): (Pattern, Map[Variable, Expr]) = {
        val (ids, binders, exprs, tps, subPatterns, builder) = deconstructor.deconstruct(pattern)

        val widenedBinders = binders.map(binder => widenBinder(binder.toVal))
        val newBinders = binders.zip(widenedBinders).map { case (binder, widened) => widened.fold(binder)(_._1.toVariable) }
        val binderSubstitution: Map[Variable, Expr] = widenedBinders.flatten.map(_._2).toMap

        val widenedSubPatterns = subPatterns.map(widenPatternBinders)
        val substitution = widenedSubPatterns.foldLeft(binderSubstitution)(_ ++ _._2)

        (builder(ids, newBinders, exprs, tps, widenedSubPatterns.map(_._1)).copiedFrom(pattern), substitution)
      }

      def rewrittenResultType(e: Expr): Type = e match {
        case Let(_, _, body) => rewrittenResultType(body)
        case LetVar(_, _, body) => rewrittenResultType(body)
        case Block(_, last) => rewrittenResultType(last)
        case _ => e.getType
      }

      object transformer extends ConcreteOOSelfTreeTransformer {
        def rewriteBinding(vd: ValDef, value: Expr, body: Expr)(rebuild: (ValDef, Expr, Expr) => Expr): Expr = widenBinder(vd) match {
          case None =>
            rebuild(vd, transform(value), transform(body))

          case Some((newVd, substitution)) =>
            val substitutedBody = exprOps.replaceFromSymbols(Map(substitution), body)
            rebuild(newVd, transform(value), rewriteBody(substitutedBody, freshLocals, locals, widenedVarIds + vd.id))
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
            substitutedGuard.map(guard => rewriteBody(guard, freshLocals, locals, newWidenedIds)),
            rewriteBody(substitutedRhs, freshLocals, locals, newWidenedIds)
          ).copiedFrom(matchCase)
        }

        override def transform(e: Expr): Expr = e match {
          case Return(_) if freshLocals.isEmpty => super.transform(e)

          case ret @ Return(retExpr) =>
            Return(Tuple(freshLocals.map(_.setPos(ret)) :+ transform(retExpr)).setPos(ret)).setPos(ret)

          case l @ LetRec(fds, letBody) =>
            val newLocals = locals ++ fds.map(f => f.id -> f)
            val nfds = fds.map(fd => rewriteFunction(Inner(fd), newLocals, widenedVarIds).toLocal)
            LetRec(nfds, rewriteBody(letBody, freshLocals, newLocals, widenedVarIds)).copiedFrom(l)

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
            val rewritten = rewriteBody(substitutedBody, freshLocals, locals, widenedVarIds)
            val resultType = rewrittenResultType(rewritten)

            Lambda(params, withReturnedCopies(aliasedParams, copies, rewritten, resultType, lambdaBody)).copiedFrom(l)

          case FunctionInvocation(unfoldId @ ast.SymbolIdentifier("stainless.lang.unfold"), Seq(_), Seq(fi: FunctionInvocation)) =>
            val callee = Outer(fi.tfd.fd)
            val call = FunctionInvocation(fi.id, fi.tps, fi.args.map(transform)).copiedFrom(fi)
            val resultType = fi.tfd.instantiate(getReturnType(callee))
            val rewrittenCall = rewriteCallEffects(callee.params, fi.args, call, resultType, effects(callee), selectResult = false)

            FunctionInvocation(unfoldId, Seq(resultType), Seq(rewrittenCall)).copiedFrom(fi)

          case fi: FunctionInvocation =>
            val callee = Outer(fi.tfd.fd)
            val call = FunctionInvocation(fi.id, fi.tps, fi.args.map(transform)).copiedFrom(fi)
            val resultType = fi.tfd.instantiate(getReturnType(callee))
            rewriteCallEffects(callee.params, fi.args, call, resultType, effects(callee), selectResult = true)

          case application @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val callee = Inner(locals(id))
            val calleeType = FunctionType(callee.params.map(_.getType), getReturnType(callee)).copiedFrom(tpe)
            val call = ApplyLetRec(id, tparams, calleeType, tps, args.map(transform)).copiedFrom(application)
            val resultType = typeOps.instantiateType(getReturnType(callee), (tparams zip tps).toMap)
            rewriteCallEffects(callee.params, args, call, resultType, effects(callee), selectResult = true)

          case application @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType: @unchecked
            val call = Application(transform(callee), args.map(transform)).copiedFrom(application)
            val calleeEffects = functionTypeEffects(ft)
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
            rewriteCallEffects(params, args, call, resultType, paramEffects.toSet, selectResult = true)

          case _ => super.transform(e)
        }
      }

      transformer.transform(body)
    }

    private def rewriteCallEffects(
      formalParams: Seq[ValDef],
      args: Seq[Expr],
      call: Expr,
      resultType: Type,
      calleeEffects: Set[Effect],
      selectResult: Boolean
    ): Expr = {
      val localEffects = formalParams.zip(args)
        .map { case (vd, arg) => (vd.toVariable, calleeEffects.filter(_.receiver == vd.toVariable), arg) }
        .filter { case (_, effects, _) => effects.nonEmpty }

      if (localEffects.isEmpty) {
        return call
      }

      val result = ValDef(FreshIdentifier("res"), resultType).copiedFrom(call)

      val assignments = localEffects.zipWithIndex.flatMap { case ((param, effects, arg), effectIndex) =>
        val resultSelect = TupleSelect(result.toVariable, effectIndex + 1)

        Try(ModifyingEffect(param, Path.empty).on(arg)) match {
          case Success(wholeTargets) =>
            wholeTargets.toSeq.map { case (effect, effectCondition) =>
              makeAssignment(arg.getPos, resultSelect, Seq.empty, effect.toTarget(effectCondition))
            }

          case Failure(_) =>
            effects.toSeq.flatMap { calleeEffect =>
              (calleeEffect `on` arg).toSeq.map { case (argumentEffect, effectCondition) =>
                val knownCalleeEffect = calleeEffect.removeUnknownAccessor
                val knownArgumentEffect = argumentEffect.removeUnknownAccessor
                makeAssignment(arg.getPos, resultSelect, knownCalleeEffect.path.path, knownArgumentEffect.toTarget(effectCondition))
              }
            }
        }
      }

      val resultExpr =
        if (selectResult) TupleSelect(result.toVariable, localEffects.length + 1)
        else result.toVariable

      Let(result, call, Block(assignments, resultExpr))
    }

    private def makeAssignment(pos: inox.utils.Position, resultSelect: Expr, outerPath: Seq[Accessor], target: Target): Expr = {
      def select(tpe: Type, expr: Expr, path: Seq[Accessor]): (Expr, Expr) = (tpe, path) match {
        case (adt: ADTType, ADTFieldAccessor(id) +: rest) =>
          val constructors = adt.getSort.constructors
          val constructor = constructors.find(_.fields.exists(_.id == id)).get
          val field = constructor.fields.find(_.id == id).get

          val condition = if (constructors.size > 1) {
            IsConstructor(expr, constructor.id).setPos(pos)
          } else {
            BooleanLiteral(true).setPos(pos)
          }

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
            val updatedField = if (isFinal) updatedPath(ClassSelector(casted, selector.id), rest)
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

          case Nil => newValue
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

      val (condition, result) = select(resultSelect.getType, resultSelect, outerPath)
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

    private def widenBinder(vd: ValDef): Option[(ValDef, (Variable, Expr))] = {
      val widenedTpe = transformer.transform(vd.tpe)
      if (widenedTpe == vd.tpe) {
        return None
      }

      val newVd = vd.copy(tpe = widenedTpe).copiedFrom(vd)
      Some((newVd, (vd.toVariable, newVd.toVariable)))
    }

    private def copiesOf(aliasedParams: Seq[ValDef]): (Seq[ValDef], Map[Variable, Expr]) = {
      val copies = aliasedParams.map(_.freshen)
      val substitution: Map[Variable, Expr] = aliasedParams.zip(copies).map { case (param, copy) => param.toVariable -> copy.toVariable }.toMap

      (copies, substitution)
    }

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
  case class SummaryData(affectedFns: Set[Identifier] = Set.empty) {
    def ++(other: SummaryData): SummaryData = SummaryData(affectedFns ++ other.affectedFns)
    def hasRun: Boolean = affectedFns.nonEmpty
  }

  override val name: String = "FunctionRewrite"

  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends FunctionRewrite(s)(t)
    new Impl(trees, trees)
  }
}
