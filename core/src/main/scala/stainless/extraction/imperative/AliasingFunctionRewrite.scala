/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

import scala.util.{Failure, Success, Try}

trait CallResults { self =>
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

class AliasingFunctionRewrite(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with EffectsAnalyzer
     with EffectsChecker
     with GhostChecker
     with CallResults { self =>
  import s._
  import exprOps._

  // Same dependency-cache rationale as AntiAliasing: rewriting depends on the
  // effects analysis, which relies on the function's full dependency graph.
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

  protected case class SymbolsAnalysis()(using override val symbols: Symbols) extends EffectsAnalysis {
    import symbols._

    // Convert a function type with mutable parameters, into a function type
    // that returns the mutable parameters. This makes explicit all possible
    // effects of the function. This should be used for higher order functions
    // declared as parameters.
    def makeFunctionTypeExplicit(tpe: Type): Type =
      def makeSigmaType(mutableParams: Seq[Type], returnType: Type) =
        val freshParams = mutableParams.map(tpe => ValDef(FreshIdentifier("x"), tpe))
        sigmaTypeWrap(freshParams, returnType).copiedFrom(returnType)

      tpe match {
       case ft @ FunctionType(from, to) =>
        val mutableParams = from.filter(isMutableType(_))
        if mutableParams.isEmpty then ft
        else ft.copy(to = makeSigmaType(mutableParams, to)).copiedFrom(ft)

       case pt @ PiType(params, to) =>
        val mutableParamTypes = params.map(_.tpe).filter(isMutableType(_))
        if mutableParamTypes.isEmpty then pt
        else pt.copy(to = makeSigmaType(mutableParamTypes, to)).copiedFrom(pt)
     }

    object transformer extends ConcreteOOSelfTreeTransformer {

      // XXX: since ApplyLetRec stores the type of the corresponding function,
      //      we have to make sure to NOT make that first-class function type explicit!!
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
  }

  override protected type TransformerContext = SymbolsAnalysis
  override protected def getContext(symbols: Symbols) = SymbolsAnalysis()(using symbols)

  enum FunctionSummary {
    case Untransformed(fid: Identifier)
    case Transformed(fid: Identifier)
  }

  override protected def extractFunction(analysis: SymbolsAnalysis, fd: FunDef): (Option[FunDef], FunctionSummary) = {
    import analysis.{given, _}
    import symbols._

    checkGhost(fd)(analysis)

    checkEffects(fd)(analysis) match {
      case CheckResult.Ok => ()
      case CheckResult.Skip => return (None, FunctionSummary.Untransformed(fd.id))
      case CheckResult.Error(_) => ()
    }

    // Utility function that essentially creates an expression representing the update of `target` with `resSelect`.
    // Ported verbatim from AntiAliasing's `select` -- it is already self-contained (no environment/aliasing lookup).
    def select(pos: inox.utils.Position, tpe: Type, expr: Expr, path: Seq[Accessor]): (Expr, Expr) = (tpe, path) match {
      case (adt: ADTType, ADTFieldAccessor(id) +: xs) =>
        val constructors = adt.getSort.constructors
        val constructor = constructors.find(_.fields.exists(_.id == id)).get
        val field = constructor.fields.find(_.id == id).get

        val condition = if (constructors.size > 1) {
          IsConstructor(expr, constructor.id).setPos(pos)
        } else {
          BooleanLiteral(true).setPos(pos)
        }

        val (recCond, recSelect) = select(pos, field.tpe, ADTSelector(expr, id).setPos(pos), xs)
        (and(condition, recCond), recSelect)

      case (ct: ClassType, ClassFieldAccessor(id) +: xs) =>
        val field = getClassField(ct, id).get
        val fieldClassType = classForField(ct, id).get.toType
        val condition = if (ct.tcd.cd.parents.isEmpty && ct.tcd.cd.children.isEmpty) BooleanLiteral(true).setPos(pos)
          else IsInstanceOf(expr, fieldClassType).setPos(pos)
        val casted = if (ct.tcd.cd.parents.isEmpty && ct.tcd.cd.children.isEmpty) expr
          else AsInstanceOf(expr, fieldClassType).setPos(expr)

        val (recCond, recSelect) = select(pos, field.tpe, ClassSelector(casted, id).setPos(pos), xs)
        (and(condition, recCond), recSelect)

      case (tt: TupleType, TupleFieldAccessor(idx) +: xs) =>
        select(pos, tt.bases(idx - 1), TupleSelect(expr, idx).setPos(pos), xs)

      case (ArrayType(base), ArrayAccessor(idx) +: xs) =>
        select(pos, base, ArraySelect(expr, idx).setPos(pos), xs)

      case (MutableMapType(from, to), MutableMapAccessor(idx) +: xs) =>
        select(pos, to, MutableMapApply(expr, idx).setPos(pos), xs)

      case (_, Nil) => (BooleanLiteral(true).setPos(pos), expr)

      case (_, _) => throw MatchError(s"Cannot select $path on type $tpe", pos)
    }

    // Rebuilds `target`'s receiver functionally, with the path of `target` replaced by `newValue`.
    // Ported verbatim from AntiAliasing's `updatedTarget`.
    def updatedTarget(target: Target, newValue: Expr): Expr = {
      def rec(receiver: Expr, path: Seq[Accessor]): Expr = path match {
        case ADTFieldAccessor(id) :: fs =>
          val adt @ ADTType(_, tps) = receiver.getType: @unchecked
          val tcons = adt.getSort.constructors.find(_.fields.exists(_.id == id)).get
          val r = rec(Annotated(ADTSelector(receiver, id).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), fs)

          ADT(tcons.id, tps, tcons.definition.fields.map { vd =>
            if (vd.id == id) freshenLocals(r)
            else freshenLocals(Annotated(ADTSelector(receiver, vd.id).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
          }).copiedFrom(newValue)

        case ClassFieldAccessor(id) :: fs =>
          val optCd = receiver.getType match {
            case ct: ClassType => classForField(ct, id)
            case tp => throw FatalError(s"Cannot apply ClassFieldAccessor to type $tp")
          }

          val (cd, ct) = optCd.map(cd => (cd, cd.toType)).getOrElse {
            throw FatalError(s"Could not find class for type ${receiver.getType}")
          }

          val casted = if (cd.parents.isEmpty && cd.children.isEmpty) receiver
            else AsInstanceOf(receiver, cd.toType).copiedFrom(receiver)
          val annotated = if (cd.parents.isEmpty && cd.children.isEmpty) rec(ClassSelector(casted, id), fs)
            else rec(Annotated(ClassSelector(casted, id).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), fs)

          ClassConstructor(ct, ct.tcd.fields.map { vd =>
            if (vd.id == id) freshenLocals(annotated)
            else if (cd.parents.isEmpty && cd.children.isEmpty) ClassSelector(freshenLocals(casted), vd.id)
            else freshenLocals(Annotated(ClassSelector(casted, vd.id).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
          }).copiedFrom(newValue)

        case TupleFieldAccessor(index) :: fs =>
          val tt @ TupleType(_) = receiver.getType: @unchecked
          val r = rec(Annotated(TupleSelect(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), fs)

          Tuple((1 to tt.dimension).map { i =>
            if (i == index) freshenLocals(r)
            else freshenLocals(Annotated(TupleSelect(receiver, i).copiedFrom(receiver), Seq(DropVCs)).copiedFrom(receiver))
          }).copiedFrom(newValue)

        case ArrayAccessor(index) :: fs =>
          val r = freshenLocals(rec(Annotated(ArraySelect(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), fs))
          freshenLocals(ArrayUpdated(receiver, index, r).copiedFrom(newValue))

        case MutableMapAccessor(index) :: fs =>
          val r = freshenLocals(rec(Annotated(MutableMapApply(receiver, index).copiedFrom(newValue), Seq(DropVCs)).copiedFrom(newValue), fs))
          freshenLocals(MutableMapUpdated(receiver, freshenLocals(index), r).copiedFrom(newValue))

        case Nil => newValue
      }

      target match {
        case Target(receiver, None, path) =>
          rec(receiver, path.toSeq)

        case Target(receiver, Some(BooleanLiteral(true)), path) =>
          rec(receiver, path.toSeq)

        case Target(receiver, Some(condition), path) if effects(condition).nonEmpty =>
          throw MalformedStainlessCode(condition, s"Effects are not allowed in condition of effects: ${condition.asString}")

        case Target(receiver, Some(condition), path) =>
          val recRecv = rec(receiver, path.toSeq)
          Annotated(
            AsInstanceOf(
              IfExpr(
                condition.setPos(newValue),
                Annotated(recRecv, Seq(DropVCs)).copiedFrom(recRecv),
                receiver
              ).copiedFrom(newValue),
              receiver.getType
            ).copiedFrom(newValue),
            Seq(DropVCs)
          ).copiedFrom(newValue)
      }
    }

    // Builds an assignment of `target` with the value at `outerPath` of `resSelect`.
    // `dropVcs` is always true here: the correctness of the mutation was already checked
    // inside the called function, so we don't want to re-verify it at the call site.
    def makeAssignment(pos: inox.utils.Position, resSelect: Expr, outerPath: Seq[Accessor], target: Target, dropVcs: Boolean = true): Expr = {
      def wrap(e: Expr): Expr = if (dropVcs) Annotated(e, Seq(DropVCs)).copiedFrom(e) else e
      def wrapCallResult(e: Expr): Expr = Annotated(e, (if (dropVcs) Seq(DropVCs) else Seq.empty) :+ CallResult.flag).copiedFrom(e)

      def writtenLocation(path: Seq[Accessor]): Expr = Path(path).wrap(target.receiver) match {
        case Some(location) if path.isEmpty || isMutableType(location.getType) => location
        case _ => writtenLocation(path.init)
      }

      val (cond, result) = select(pos, resSelect.getType, resSelect, outerPath)
      val combinedCond = andJoin(cond +: target.condition.toSeq)

      // We only overwrite the receiver when it is an actual mutable type.
      // This is necessary to handle immutable types being upcasted to `Any`, which is mutable.
      if (combinedCond != BooleanLiteral(false) && isMutableType(target.receiver.getType)) {
        val newValue = updatedTarget(target.copy(condition = Some(combinedCond)), wrapCallResult(result))
        val recvTpe = target.receiver.getType
        val castedValue =
          if (recvTpe.isInstanceOf[ADTType] && recvTpe.asInstanceOf[ADTType].getSort.constructors.size == 1)
            newValue
          else
            wrap(AsInstanceOf(newValue, recvTpe).copiedFrom(newValue))
        Assignment(target.receiver, Annotated(castedValue, Seq(WriteBack.flag(writtenLocation(target.path.toSeq)))).copiedFrom(castedValue)).setPos(pos)
      } else {
        UnitLiteral().setPos(pos)
      }
    }

    // Rewrites a call's mutating effects into a write-back of the *direct* target of each
    // affected argument only (e.g. for `f(obj.field)`, writes back into `obj.field` itself).
    //
    // Unlike AntiAliasing's `mapApplication`, this does NOT chase other local variables that
    // might also alias that argument (which would require tracking every `Let` binding across
    // the whole function body, the way AntiAliasing's `env.targets` does). That's deliberately
    // left to AliasingAssignRewrite, which runs right after this phase: it sees the plain
    // `Assignment` produced below like any other mutation, and refreshes whatever else aliases
    // it, using its own independent heap-approximation analysis. Splitting the work this way
    // avoids tracking aliasing twice.
    def rewriteCallEffects(
      formalParams: Seq[ValDef],
      args: Seq[Expr],
      nfi: Expr,
      nfiType: Type,
      fnEffects: Set[Effect],
      selectResult: Boolean
    ): Expr = {
      val localEffects = formalParams.zip(args)
        .map { case (vd, arg) => (vd.toVariable, fnEffects.filter(_.receiver == vd.toVariable), arg) }
        .filter { case (_, effects, _) => effects.nonEmpty }

      if (localEffects.isEmpty) {
        nfi
      } else {
        val freshRes = ValDef(FreshIdentifier("res"), nfiType).copiedFrom(nfi)

        val assgns = localEffects.zipWithIndex.flatMap { case ((vd, effects, arg), effIndex) =>
          // +1 because we are a tuple (1-based indexing starts at 1 for the first state)
          val resSelect = TupleSelect(freshRes.toVariable, effIndex + 1)

          // The called function always returns the *whole* new value of `vd` in this tuple slot
          // (regardless of how deep its effects on `vd` actually reach), so we first try writing
          // that whole value back wherever `vd` maps to within `arg`'s own structure (e.g. a bare
          // variable, or a field-access chain: `Path.empty` on `vd` still gets projected through
          // `arg`'s shape by `on`). If `arg` isn't itself an assignable location as a whole (e.g.
          // a fresh constructor call like `RefRef(lhsAlias, rhsAlias)`), we fall back to applying
          // each concrete effect individually, selecting just that piece out of `resSelect`.
          Try(ModifyingEffect(vd, Path.empty).on(arg)) match {
            case Success(wholeTargets) =>
              wholeTargets.toSeq.map { case (effect, effectCond) =>
                makeAssignment(arg.getPos, resSelect, Seq.empty, effect.toTarget(effectCond))
              }
            case Failure(_) =>
              effects.toSeq.flatMap { outerEffect0 =>
                (outerEffect0 `on` arg).toSeq.map { case (effect0, effectCond) =>
                  val outerEffect = outerEffect0.removeUnknownAccessor
                  val effect = effect0.removeUnknownAccessor
                  makeAssignment(arg.getPos, resSelect, outerEffect.path.path, effect.toTarget(effectCond))
                }
              }
          }
        }

        val exprRes =
          if (selectResult) TupleSelect(freshRes.toVariable, localEffects.length + 1)
          else freshRes.toVariable

        Let(freshRes, nfi, Block(assgns, exprRes))
      }
    }

    type Locals = Map[Identifier, LocalFunDef]

    // Widens a single binder's declared type the same way `widenedParams` widens a
    // FunDef param: a `Let`/`LetVar`/pattern binder's `ValDef.tpe` is embedded
    // directly on the node (unlike e.g. a `ClassSelector`'s type, which is looked
    // up dynamically against the final, already-widened `Symbols` at
    // `ensureWellFormed` time), so if it declares a function type that
    // `rewriteBody`'s `Lambda`/`Application` cases would widen for any *value*
    // flowing through it, the declaration itself -- and every `Variable`
    // occurrence copying its `tpe` field -- must be widened too, or the rewritten
    // tree stops type-checking (the binder/use-sites keep advertising the old,
    // narrower type while the value bound to them is already the wider one).
    // Returns `None` if `vd`'s type needs no widening (the common case).
    def widenBinder(vd: ValDef): Option[(ValDef, (Variable, Expr))] = {
      val widenedTpe = analysis.transformer.transform(vd.tpe)
      if (widenedTpe == vd.tpe) None
      else {
        val newVd = vd.copy(tpe = widenedTpe).copiedFrom(vd)
        Some((newVd, (vd.toVariable, newVd.toVariable)))
      }
    }

    // Recursively widens every binder in a pattern (e.g. `case FunctionWrapper(f) => ...`
    // binding `f: (A) => Int` when `A` is mutable), mirroring `widenBinder` above for
    // the (possibly several) `ValDef`s a pattern can introduce.
    def widenPatternBinders(pattern: Pattern): (Pattern, Map[Variable, Expr]) = {
      def go(binder: Option[ValDef]): (Option[ValDef], Map[Variable, Expr]) = binder match {
        case Some(vd) =>
          widenBinder(vd) match {
            case Some((newVd, subst)) => (Some(newVd), Map(subst))
            case None => (Some(vd), Map.empty)
          }
        case None => (None, Map.empty)
      }
      def recSubs(subs: Seq[Pattern]): (Seq[Pattern], Map[Variable, Expr]) = {
        val recs = subs.map(widenPatternBinders)
        (recs.map(_._1), recs.foldLeft(Map.empty[Variable, Expr])(_ ++ _._2))
      }

      pattern match {
        case p @ WildcardPattern(binder) =>
          val (nb, subst) = go(binder)
          (WildcardPattern(nb).copiedFrom(p), subst)

        case p @ ADTPattern(binder, id, tps, subs) =>
          val (nb, subst0) = go(binder)
          val (newSubs, subst1) = recSubs(subs)
          (ADTPattern(nb, id, tps, newSubs).copiedFrom(p), subst0 ++ subst1)

        case p @ TuplePattern(binder, subs) =>
          val (nb, subst0) = go(binder)
          val (newSubs, subst1) = recSubs(subs)
          (TuplePattern(nb, newSubs).copiedFrom(p), subst0 ++ subst1)

        case p @ LiteralPattern(binder, lit) =>
          val (nb, subst0) = go(binder)
          (LiteralPattern(nb, lit).copiedFrom(p), subst0)

        case p @ UnapplyPattern(binder, recs, id, tps, subs) =>
          val (nb, subst0) = go(binder)
          val (newSubs, subst1) = recSubs(subs)
          (UnapplyPattern(nb, recs, id, tps, newSubs).copiedFrom(p), subst0 ++ subst1)

        case p @ AlternativePattern(binder, subs) =>
          val (nb, subst0) = go(binder)
          val (newSubs, subst1) = recSubs(subs)
          (AlternativePattern(nb, newSubs).copiedFrom(p), subst0 ++ subst1)

        case p @ RefinementPattern(underlying, pred) =>
          val (nu, subst0) = widenPatternBinders(underlying)
          (RefinementPattern(nu, pred).copiedFrom(p), subst0)

        // `oo.Trees` (which `imperative.Trees` extends) adds two more pattern
        // kinds on top of the base `ast.Expressions.Pattern` variants matched
        // above: `ClassPattern` for `case binder @ ct(subPatterns...) =>` (e.g.
        // deconstructing a plain, single-constructor case class like
        // `FunctionWrapper`, as opposed to `ADTPattern` for a sealed-sort
        // constructor) and `InstanceOfPattern` for `case binder: ct`. Both need
        // the same binder-widening treatment as every other pattern kind above.
        case p @ ClassPattern(binder, tpe, subs) =>
          val (nb, subst0) = go(binder)
          val (newSubs, subst1) = recSubs(subs)
          (ClassPattern(nb, tpe, newSubs).copiedFrom(p), subst0 ++ subst1)

        case p @ InstanceOfPattern(binder, tpe) =>
          val (nb, subst0) = go(binder)
          (InstanceOfPattern(nb, tpe).copiedFrom(p), subst0)
      }
    }

    // Reads off the "real" type of an already-`rewriteBody`-transformed expression, for cases
    // (like the aliased-params `Lambda` case below) that need to declare a `ValDef`'s type from
    // a rewritten subtree's result, WITHOUT trusting that subtree's own top-level `.getType`.
    //
    // `rewriteCallEffects` (used by the `FunctionInvocation`/`ApplyLetRec` cases) always wraps a
    // rewritten call site as `Let(freshRes, nfi, Block(assgns, exprRes))`, where `freshRes` is
    // explicitly declared with the CALLEE's correct widened return type (`nfiType`, derived from
    // `analysis.getReturnType`) -- the same widened type that callee's own `FunDef.returnType`
    // will carry in this phase's FINAL output `Symbols`. But `nfi` is still a bare, unrewritten
    // `FunctionInvocation`/`ApplyLetRec` node, and its OWN structural `.getType` resolves the
    // callee against `analysis.symbols`, which stays fixed to this phase's ORIGINAL, pre-rewrite
    // input snapshot for the entire run (`getContext` builds `analysis` once, up front) -- so it
    // always reports that callee's OLD, narrow return type, never the new widened one, no matter
    // when during this phase you ask. `Let.computeTpe` then spuriously computes `Untyped` for the
    // whole `Let` (its own subtype check, `nfi.getType` vs `freshRes`'s declared type, fails),
    // even though the expression is perfectly well-typed once checked against the FINAL `Symbols`
    // (exactly what `ensureWellFormed` does, once this whole phase -- not just this one function --
    // has finished). Skip past that (and any `LetVar`/`Block` wrapped around it the same way,
    // e.g. by `Swap`) straight to the actual final sub-expression, and trust *that* one's own
    // `.getType` instead of the wrapper's spuriously pessimistic one.
    //
    // This is safe to do for an `Application` of a first-class HOF variable too (e.g. `ping`/
    // `get` in `Lambda3.scala`'s `app`, whose own effects are rewritten by the `Application` case
    // instead of `FunctionInvocation`): `Application.computeTpe` just echoes its callee's own
    // (embedded-on-the-node, symbols-independent) type directly, with no separate subtype check,
    // so it never hits this mismatch in the first place -- unwrapping through it here is a no-op.
    def rewrittenResultType(e: Expr): Type = e match {
      case Let(_, _, body) => rewrittenResultType(body)
      case LetVar(_, _, body) => rewrittenResultType(body)
      case Block(_, last) => rewrittenResultType(last)
      case _ => e.getType
    }

    // Walks a function/lambda body, rewriting `Return`s to match the (possibly tuple-wrapped)
    // new return type, local recursive functions and lambdas to make their own aliasing
    // effects explicit, and call sites to write back their effects (see `rewriteCallEffects`).
    // Everything else -- including `FieldAssignment`/`ArrayUpdate`/`Let` -- is left untouched;
    // that in-body mutation rewriting is AliasingAssignRewrite's job.
    def rewriteBody(body: Expr, freshLocals: Seq[Variable], locals: Locals, widenedVarIds: Set[Identifier]): Expr = {
      class BodyTransformer extends ConcreteOOSelfTreeTransformer {
        override def transform(e: Expr): Expr = e match {
          case ret @ Return(_) if freshLocals.isEmpty => super.transform(e)

          case ret @ Return(retExpr) =>
            Return(Tuple(freshLocals.map(_.setPos(ret)) :+ transform(retExpr)).setPos(ret)).setPos(ret)

          case l @ LetRec(fds, letBody) =>
            val newLocals = locals ++ fds.map(f => f.id -> f)
            val nfds = fds.map(fd => updateFunction(Inner(fd), newLocals, widenedVarIds).toLocal)
            LetRec(nfds, rewriteBody(letBody, freshLocals, newLocals, widenedVarIds)).copiedFrom(l)

          // A postcondition predicate must keep its declared shape `(T) => Boolean`
          // (see `Ensuring.computeTpe`): its own effects, if any, are already
          // accounted for by its enclosing function's own aliased-params tupling
          // (handled separately in `updateFunction`'s `newSpecs`, which never
          // routes the unwrapped predicate body back through this generic `Lambda`
          // case). Without this case, a postcondition whose `res` happens to have
          // a mutable type (e.g. `def foo(): Array[Int] = ...ensuring(res => ...)`)
          // would fall through to the generic `Lambda` case below and get wrongly
          // tupled into `(T) => (T, Boolean)`, breaking `Ensuring`'s own type rule
          // regardless of whether the predicate actually "mutates" anything --
          // spec lambdas aren't first-class closures called elsewhere, so
          // `functionTypeEffects`'s type-level (not implementation-level)
          // approximation doesn't apply to them the way it does to a real closure.
          case ens @ Ensuring(ensBody, pred @ Lambda(Seq(resVd), predBody)) =>
            Ensuring(transform(ensBody), Lambda(Seq(resVd), transform(predBody)).copiedFrom(pred)).copiedFrom(ens)

          // Same rationale as `widenBinder`/`widenPatternBinders` above: a plain
          // local `val`/`var` whose declared type is a function type over a
          // mutable parameter needs that declared type -- and every `Variable`
          // occurrence referencing it -- widened in lockstep with the
          // already-correctly-widened `Lambda`/call-result value now bound to it.
          case l @ Let(vd, value, letBody) =>
            widenBinder(vd) match {
              case None => Let(vd, transform(value), transform(letBody)).copiedFrom(l)
              case Some((newVd, subst)) =>
                val substBody = exprOps.replaceFromSymbols(Map(subst), letBody)
                Let(newVd, transform(value), rewriteBody(substBody, freshLocals, locals, widenedVarIds + vd.id)).copiedFrom(l)
            }

          case l @ LetVar(vd, value, letBody) =>
            widenBinder(vd) match {
              case None => LetVar(vd, transform(value), transform(letBody)).copiedFrom(l)
              case Some((newVd, subst)) =>
                val substBody = exprOps.replaceFromSymbols(Map(subst), letBody)
                LetVar(newVd, transform(value), rewriteBody(substBody, freshLocals, locals, widenedVarIds + vd.id)).copiedFrom(l)
            }

          case m @ MatchExpr(scrutinee, cases) =>
            val newCases = cases.map { mc =>
              val (newPattern, subst) = widenPatternBinders(mc.pattern)
              if (subst.isEmpty) {
                MatchCase(mc.pattern, mc.optGuard.map(transform), transform(mc.rhs)).copiedFrom(mc)
              } else {
                val newWidenedIds = widenedVarIds ++ subst.keys.map(_.id)
                val substGuard = mc.optGuard.map(g => exprOps.replaceFromSymbols(subst, g))
                val substRhs = exprOps.replaceFromSymbols(subst, mc.rhs)
                MatchCase(
                  newPattern,
                  substGuard.map(g => rewriteBody(g, freshLocals, locals, newWidenedIds)),
                  rewriteBody(substRhs, freshLocals, locals, newWidenedIds)
                ).copiedFrom(mc)
              }
            }
            MatchExpr(transform(scrutinee), newCases).copiedFrom(m)

          case l @ Lambda(params, lambdaBody) =>
            // Deliberately NOT `l.getType` here (which would recompute the whole
            // subtree's type, including `lambdaBody`'s): `functionTypeEffects` only
            // ever looks at a function type's `from` (see its definition -- `to` is
            // unused), so we can read `ownEffects` straight off `params` without
            // forcing `lambdaBody.getType`. Forcing it is actively unsafe at this
            // point in the walk: `widenedFullBody`/`widenedVarIds` in `updateFunction`
            // already substituted any widened HOF-typed variables (e.g. a mutable-
            // type-parameter'd `ping`/`get`) throughout the ENTIRE body up front,
            // before this top-down walk gets a chance to rewrite their call sites
            // (the `Application`/`FunctionInvocation` cases below) -- so a nested
            // `Application` of one of those not-yet-rewritten variables is
            // structurally mistyped (its callee now advertises the widened
            // tuple-returning type while the `Application` node still expects the
            // old one), and `computeTpe` reports `Untyped` for it, which propagates
            // up through `lambdaBody.getType` and then, via `FunctionType`'s own
            // `unveilUntyped`, collapses `l.getType` itself to plain `Untyped`
            // (rather than `FunctionType(_, Untyped)`) -- so the
            // `FunctionType(_, _)` pattern below would fail with a `MatchError`.
            val ownEffects: Set[Int] = params.zipWithIndex.collect {
              case (vd, i) if isMutableType(vd.tpe) => i
            }.toSet
            val aliasedParams: Seq[ValDef] = params.zipWithIndex.flatMap {
              case (vd, i) if ownEffects.contains(i) => Some(vd)
              case _ => None
            }

            if (aliasedParams.isEmpty) {
              Lambda(params, transform(lambdaBody)).copiedFrom(l)
            } else {
              val freshP = aliasedParams.map(_.freshen)
              val subst = aliasedParams.zip(freshP).map(p => p._1.toVariable -> p._2.toVariable).toMap
              val freshBody = exprOps.replaceFromSymbols(subst, lambdaBody)

              // Rewrite (nested calls/lambdas/Returns/etc.) BEFORE computing its
              // type: same reasoning as `ownEffects` above -- `freshBody` can
              // itself directly apply an outer widened HOF param (as `ping`/`get`
              // do in `Lambda3.scala`'s `app`), which is only well-typed again
              // *after* the Application/FunctionInvocation cases below have run
              // on it, so computing its declared result type (formerly `ft.to`,
              // read off the untransformed `l.getType`) has to happen on the
              // rewritten tree, not the raw one.
              val rewrittenFreshBody = rewriteBody(freshBody, freshLocals, locals, widenedVarIds)
              val tmp = ValDef(FreshIdentifier("res"), rewrittenResultType(rewrittenFreshBody))
              val finalBody: Expr =
                Let(tmp, rewrittenFreshBody, Tuple(freshP.map(_.toVariable) :+ tmp.toVariable).copiedFrom(lambdaBody)).copiedFrom(lambdaBody)

              // No further `rewriteBody` pass needed here: `rewrittenFreshBody` is
              // already fully rewritten above, and the `Let`/`LetVar` wrapping built
              // below is new, hand-constructed scaffolding (`tmp`/`freshP` are never
              // function-typed -- `isMutableType` never treats a `FunctionType`
              // itself as mutable, see `SymbolOps.isMutableType` -- so neither needs
              // `widenBinder`'s widening). Re-running the whole thing through
              // `rewriteBody` a second time, as the old code did, would re-walk
              // `rewrittenFreshBody`'s own already-widened call sites and (per the
              // `widenedVarIds`-aware `Application` case's own comment) double-wrap
              // their types.
              val wrappedBody: Expr = freshP.zip(aliasedParams).foldLeft(finalBody) {
                (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(bd)
              }
              Lambda(params, wrappedBody).copiedFrom(l)
            }

          case fi: FunctionInvocation =>
            val callee = Outer(fi.tfd.fd)
            val nfi = FunctionInvocation(fi.id, fi.tps, fi.args.map(transform)).copiedFrom(fi)
            val nfiType = fi.tfd.instantiate(analysis.getReturnType(callee))
            rewriteCallEffects(callee.params, fi.args, nfi, nfiType, effects(callee), selectResult = true)

          case alr @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val callee = Inner(locals(id))
            val nfi = ApplyLetRec(
              id, tparams,
              FunctionType(callee.params.map(_.getType), analysis.getReturnType(callee)).copiedFrom(tpe), tps,
              args.map(transform)
            ).copiedFrom(alr)
            val resultType = typeOps.instantiateType(analysis.getReturnType(callee), (tparams zip tps).toMap)
            rewriteCallEffects(callee.params, args, nfi, resultType, effects(callee), selectResult = true)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType: @unchecked
            val ftEffects = functionTypeEffects(ft)
            if (ftEffects.nonEmpty) {
              val nfi = Application(transform(callee), args.map(transform)).copiedFrom(app)

              val params = from.map(tpe => ValDef.fresh("x", tpe))
              val appEffects = params.zipWithIndex.collect {
                case (vd, i) if ftEffects(i) => ModifyingEffect(vd.toVariable, Path.empty)
              }
              // `callee.getType` is computed against `analysis.symbols`, i.e. the ORIGINAL
              // (pre-widening) declarations, for anything whose type isn't embedded directly
              // on the expression node itself (e.g. a `ClassSelector`/`ADTSelector` field
              // read, or a `Lambda` literal used directly as the callee, whose `getType` here
              // is computed from its *untransformed* body) -- so `to` is still narrow and
              // needs the usual one-time widening in those cases.
              //
              // The one exception is a bare `Variable` that refers to a FunDef/local-fundef
              // parameter *this pass itself* already widened (see `updateFunction`'s
              // `widenedParams`/`paramSubst`): such a variable's `tpe` field was substituted
              // in place, so `callee.getType` already reports the widened type here, and
              // re-applying `makeFunctionTypeExplicit` would double-wrap the tuple (it only
              // looks at `from` to decide whether to widen, so it can't tell "already widened"
              // apart from "not yet widened" on its own).
              val newTo = callee match {
                case v: Variable if widenedVarIds(v.id) => to
                case _ => analysis.makeFunctionTypeExplicit(ft).asInstanceOf[FunctionType].to
              }
              rewriteCallEffects(params, args, nfi, newTo, appEffects.toSet, selectResult = true)
            } else {
              Application(transform(callee), args.map(transform)).copiedFrom(app)
            }

          // Desugars into two plain `ArrayUpdate`s so `AliasingAssignRewrite` can handle
          // each one with its ordinary (already-supported) machinery, rather than needing
          // its own dedicated Swap case. index1/index2 are hoisted into Lets (rather than
          // asserted referentially transparent, as AntiAliasing's own Swap case does)
          // since each is used twice below -- once to read the old value, once to write
          // it back; array1/array2 aren't hoisted, matching how AntiAliasing itself
          // reuses recArray1/recArray2 as-is (receiver expressions are already treated as
          // safe to duplicate throughout this subsystem -- only index/value expressions
          // get the single-evaluation treatment).
          case swap @ Swap(array1, index1, array2, index2) =>
            val recArray1 = transform(array1)
            val recArray2 = transform(array2)
            val recIndex1 = transform(index1)
            val recIndex2 = transform(index2)

            val ArrayType(base) = recArray1.getType: @unchecked
            val i1 = ValDef.fresh("i1", recIndex1.getType).setPos(swap)
            val i2 = ValDef.fresh("i2", recIndex2.getType).setPos(swap)
            val temp = ValDef.fresh("temp", base).setPos(swap)

            Let(i1, recIndex1,
              Let(i2, recIndex2,
                Let(temp, ArraySelect(recArray1, i1.toVariable).setPos(swap),
                  Block(
                    Seq(ArrayUpdate(recArray1, i1.toVariable, ArraySelect(recArray2, i2.toVariable).setPos(swap)).setPos(swap)),
                    ArrayUpdate(recArray2, i2.toVariable, temp.toVariable).setPos(swap)
                  ).setPos(swap)
                ).setPos(swap)
              ).setPos(swap)
            ).setPos(swap)

          // Same idea as `Swap` right above: desugars into two plain `FieldAssignment`s
          // (on `Cell`'s single content field) so `AliasingAssignRewrite` handles each
          // with its ordinary, already-supported `FieldAssignment` machinery -- no
          // dedicated CellSwap case needed there either. `cell1`/`cell2` aren't hoisted
          // into Lets, matching `Swap`'s own array1/array2 (receiver expressions are
          // already treated as safe to duplicate throughout this subsystem).
          case cellSwap @ CellSwap(cell1, cell2) =>
            val recCell1 = transform(cell1)
            val recCell2 = transform(cell2)

            val ct @ ClassType(_, _) = recCell1.getType: @unchecked
            val cellClassDef = symbols.lookup.get[ClassDef]("stainless.lang.Cell").get
            val vFieldId = cellClassDef.fields.head.id
            val vField = getClassField(ct, vFieldId).get

            val temp = ValDef.fresh("temp", vField.tpe).setPos(cellSwap)

            Let(temp, ClassSelector(recCell1, vFieldId).setPos(cellSwap),
              Block(
                Seq(FieldAssignment(recCell1, vFieldId, ClassSelector(recCell2, vFieldId).setPos(cellSwap)).setPos(cellSwap)),
                FieldAssignment(recCell2, vFieldId, temp.toVariable).setPos(cellSwap)
              ).setPos(cellSwap)
            ).setPos(cellSwap)

          case _ => super.transform(e)
        }
      }

      (new BodyTransformer).transform(body)
    }

    /* Create a new FunDef/local fundef for a given one in the program.
     * Adapt the signature to express its effects. In case the function has no
     * effect, this will still return the original fundef (with its body walked
     * for nested calls/lambdas/returns).
     */
    def normalizeTargets(body: Expr): Expr = {
      def bind(e: Expr, name: String): (Seq[(ValDef, Expr)], Expr) = {
        val vd = ValDef.fresh(name, e.getType).copiedFrom(e)
        (Seq(vd -> e), vd.toVariable)
      }

      def normalizeSelector(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case _: Variable | _: Literal[?] => (Seq.empty, e)
        case _ => bind(e, "index")
      }

      def normalizeForTarget(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
        case v: Variable =>
          (Seq.empty, v)
        case cs @ ClassSelector(recv, sel) =>
          val (bindings, normRecv) = normalizeForTarget(recv)
          (bindings, ClassSelector(normRecv, sel).copiedFrom(cs))
        case adt @ ADTSelector(recv, sel) =>
          val (bindings, normRecv) = normalizeForTarget(recv)
          (bindings, ADTSelector(normRecv, sel).copiedFrom(adt))
        case tpl @ TupleSelect(recv, ix) =>
          val (bindings, normRecv) = normalizeForTarget(recv)
          (bindings, TupleSelect(normRecv, ix).copiedFrom(tpl))
        case ann @ Annotated(recv, flags) =>
          val (bindings, normRecv) = normalizeForTarget(recv)
          (bindings, Annotated(normRecv, flags).copiedFrom(ann))
        case aio @ AsInstanceOf(recv, tpe) =>
          val (bindings, normRecv) = normalizeForTarget(recv)
          (bindings, AsInstanceOf(normRecv, tpe).copiedFrom(aio))
        case as @ ArraySelect(recv, i) =>
          val (bindings1, normRecv) = normalizeForTarget(recv)
          val (bindings2, normI) = normalizeSelector(i)
          (bindings1 ++ bindings2, ArraySelect(normRecv, normI).copiedFrom(as))
        case ma @ MutableMapApply(recv, k) =>
          val (bindings1, normRecv) = normalizeForTarget(recv)
          val (bindings2, normK) = normalizeSelector(k)
          (bindings1 ++ bindings2, MutableMapApply(normRecv, normK).copiedFrom(ma))
        case other =>
          bind(other, "target")
      }

      def wrap(bindings: Seq[(ValDef, Expr)], e: Expr): Option[Expr] =
        if (bindings.isEmpty) None
        else Some(bindings.foldRight(e) { case ((vd, value), body) => Let(vd, value, body).copiedFrom(e) })

      exprOps.postMap {
        case fa @ FieldAssignment(obj, sel, value) =>
          val (bindings, normObj) = normalizeForTarget(obj)
          wrap(bindings, FieldAssignment(normObj, sel, value).copiedFrom(fa))
        case au @ ArrayUpdate(array, index, value) =>
          val (bindings1, normArray) = normalizeForTarget(array)
          val (bindings2, normIndex) = normalizeSelector(index)
          wrap(bindings1 ++ bindings2, ArrayUpdate(normArray, normIndex, value).copiedFrom(au))
        case mu @ MutableMapUpdate(map, key, value) =>
          val (bindings1, normMap) = normalizeForTarget(map)
          val (bindings2, normKey) = normalizeSelector(key)
          wrap(bindings1 ++ bindings2, MutableMapUpdate(normMap, normKey, value).copiedFrom(mu))
        case swap @ Swap(array1, index1, array2, index2) =>
          val (bindings1, normArray1) = normalizeForTarget(array1)
          val (bindings2, normIndex1) = normalizeSelector(index1)
          val (bindings3, normArray2) = normalizeForTarget(array2)
          val (bindings4, normIndex2) = normalizeSelector(index2)
          wrap(bindings1 ++ bindings2 ++ bindings3 ++ bindings4, Swap(normArray1, normIndex1, normArray2, normIndex2).copiedFrom(swap))
        case cellSwap @ CellSwap(cell1, cell2) =>
          val (bindings1, normCell1) = normalizeForTarget(cell1)
          val (bindings2, normCell2) = normalizeForTarget(cell2)
          wrap(bindings1 ++ bindings2, CellSwap(normCell1, normCell2).copiedFrom(cellSwap))
        case _ =>
          None
      }(body)
    }

    def updateFunction(fd: FunAbstraction, locals: Locals, outerWidenedVarIds: Set[Identifier]): FunAbstraction = {
      val aliasedParams = analysis.getAliasedParams(fd)

      // A function-typed param (e.g. `f: (A) => Unit`) needs its DECLARED type
      // widened to the effect-tupled form too, matching what `rewriteBody`'s
      // Application/Lambda cases already assume for any value flowing through
      // it: this function's own body may call `f` expecting the tupled return,
      // and call sites now pass an already-widened lambda/closure argument (see
      // the `Lambda` case below and `extractClass`'s field widening). Without
      // this, the signature keeps advertising the old, narrower type and the
      // rewritten tree stops type-checking. `transformer.transform` is the same
      // type-widening walk already used for ClassDef/ADTSort fields, so a
      // function type nested inside e.g. a tuple/ADT param is handled too.
      val widenedParams: Seq[(ValDef, ValDef)] = fd.params.flatMap { vd =>
        val widenedTpe = analysis.transformer.transform(vd.tpe)
        if (widenedTpe != vd.tpe) Some(vd -> vd.copy(tpe = widenedTpe).copiedFrom(vd)) else None
      }
      val paramSubst: Map[Variable, Expr] = widenedParams.map { case (old, fresh) => old.toVariable -> fresh.toVariable }.toMap
      val newParams =
        if (widenedParams.isEmpty) fd.params
        else { val widenedMap = widenedParams.toMap; fd.params.map(vd => widenedMap.getOrElse(vd, vd)) }
      val widenedFullBody = normalizeTargets(
        if (paramSubst.isEmpty) fd.fullBody else exprOps.replaceFromSymbols(paramSubst, fd.fullBody))

      // Ids of params (in scope for this function's own body, including whatever the
      // caller already widened for enclosing scopes) whose `Variable` occurrences were
      // just substituted in place above to carry the widened type directly -- see the
      // `Application` case in `rewriteBody`, which needs to tell those apart from
      // e.g. a `ClassSelector`/`ADTSelector` field read or a literal `Lambda`, whose
      // `getType` still reports the narrow, not-yet-widened type at this point.
      val widenedVarIds: Set[Identifier] = outerWidenedVarIds ++ widenedParams.map(_._1.id)

      // Just like params, the DECLARED return type needs the same widening whenever it
      // is (or contains) a function type with mutable `from` params -- e.g. a case class'
      // generated `def copy$default$N(thiss: Wrapper): (A) => BigInt = thiss.f` accessor,
      // whose body now resolves against the already-widened `ClassDef` field and reports
      // `(A) => (A, BigInt)`, while its own declared return type stayed narrow. Widening
      // is applied to `analysis.getReturnType(fd)` (rather than bare `fd.returnType`)
      // so it also reaches a function type nested inside the aliased-params sigma/tuple
      // wrapping below (`transformer.transform` recurses into nested types generically).
      val newFd = fd.copy(params = newParams, returnType = analysis.transformer.transform(analysis.getReturnType(fd)))

      if (aliasedParams.isEmpty) {
        newFd.copy(fullBody = rewriteBody(widenedFullBody, Seq.empty, locals, widenedVarIds))
      } else {
        val (specs, body) = exprOps.deconstructSpecs(widenedFullBody)
        val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
        val freshSubst = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap

        val newBody = body.map { body =>
          val freshBody = exprOps.replaceFromSymbols(freshSubst, body)
          val explicitBody = rewriteBody(freshBody, freshLocals.map(_.toVariable), locals, widenedVarIds)

          val tmp = ValDef(FreshIdentifier("res"), typeOps.replaceFromSymbols(freshSubst, analysis.transformer.transform(fd.returnType)))
          val finalBody: Expr =
            Let(tmp, explicitBody, Tuple(freshLocals.map(_.toVariable) :+ tmp.toVariable).copiedFrom(body)).copiedFrom(body)

          freshLocals.zip(aliasedParams).foldLeft(finalBody) {
            (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(body)
          }
        }

        val newSpecs = specs.map {
          case exprOps.Postcondition(post @ Lambda(Seq(res), postBody)) =>
            val newRes = ValDef(res.id.freshen, newFd.returnType).copiedFrom(res)
            val newBody = exprOps.replaceSingle(
              aliasedParams.map(vd => (Old(vd.toVariable), vd.toVariable): (Expr, Expr)).toMap ++
              aliasedParams.zipWithIndex.map { case (vd, i) =>
                (vd.toVariable, TupleSelect(newRes.toVariable, i+1).copiedFrom(vd)): (Expr, Expr)
              }.toMap + (res.toVariable -> TupleSelect(newRes.toVariable, aliasedParams.length + 1).copiedFrom(res)),
              rewriteBody(postBody, Seq.empty, locals, widenedVarIds)
            )

            exprOps.Postcondition(Lambda(Seq(newRes), newBody).copiedFrom(post))

          case spec => spec
        }

        newFd.copy(fullBody = exprOps.reconstructSpecs(newSpecs, newBody, newFd.returnType))
      }
    }

    def promoteAssignedVals(body: Expr): Expr = {
      val assigned = exprOps.collect[Identifier] {
        case Assignment(v, _) => Set(v.id)
        case _ => Set.empty
      }(body)
      val promoted = exprOps.collect[Identifier] {
        case Let(vd, _, _) if assigned(vd.id) => Set(vd.id)
        case _ => Set.empty
      }(body)

      if (promoted.isEmpty) body
      else exprOps.postMap {
        case l @ Let(vd, value, rest) if promoted(vd.id) =>
          Some(LetVar(vd.toVar, value, rest).copiedFrom(l))
        case a @ Assignment(v, value) if promoted(v.id) && !v.flags.contains(IsVar) =>
          Some(Assignment(Variable(v.id, v.tpe, v.flags :+ IsVar).copiedFrom(v), value).copiedFrom(a))
        case v: Variable if promoted(v.id) && !v.flags.contains(IsVar) =>
          Some(Variable(v.id, v.tpe, v.flags :+ IsVar).copiedFrom(v))
        case _ => None
      }(body)
    }

    val newFd = updateFunction(Outer(fd), Map.empty, Set.empty).toFun
    (Some(newFd.copy(fullBody = promoteAssignedVals(newFd.fullBody)).copiedFrom(newFd)), FunctionSummary.Transformed(fd.id))
  }

  override protected type SortSummary = Unit
  override protected def extractSort(analysis: SymbolsAnalysis, sort: ADTSort): (ADTSort, Unit) =
    (analysis.transformer.transform(sort), ())

  override protected type ClassSummary = Unit
  override protected def extractClass(analysis: SymbolsAnalysis, cd: ClassDef): (ClassDef, Unit) =
    (analysis.transformer.transform(cd), ())

  override protected def combineSummaries(allSummaries: AllSummaries): ExtractionSummary = {
    val summary = allSummaries.fnsSummary.foldLeft(AliasingFunctionRewrite.SummaryData()) {
      case (summary, FunctionSummary.Untransformed(_)) => summary
      case (summary, FunctionSummary.Transformed(fid)) => summary.copy(affectedFns = summary.affectedFns + fid)
    }
    ExtractionSummary.Leaf(AliasingFunctionRewrite)(summary)
  }
}

object AliasingFunctionRewrite extends ExtractionPipelineCreator {
  case class SummaryData(affectedFns: Set[Identifier] = Set.empty) {
    def ++(other: SummaryData): SummaryData = SummaryData(affectedFns ++ other.affectedFns)
    def hasRun: Boolean = affectedFns.nonEmpty
  }

  override val name: String = "AliasingFunctionRewrite"

  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends AliasingFunctionRewrite(s)(t)
    new Impl(trees, trees)
  }
}
