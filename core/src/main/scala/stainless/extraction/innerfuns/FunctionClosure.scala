/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

class FunctionClosure(override val s: Trees, override  val t: ast.Trees)
                     (using override val context: inox.Context)
  extends CachingPhase
     with NoSummaryPhase
     with SimplyCachedFunctions
     with IdentitySorts { self =>

  // A captured variable, with the refinement of its type and, for a captured binding that is
  // bound again in the closed function rather than passed to it, the expression it is bound to.
  type RefinementVar[V] = (v: V, refine: (s.Type, Map[s.TypeParameter, s.Type]) => s.Type, definition: Option[s.Expr])

  override protected type FunctionResult = Seq[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): (Seq[t.FunDef], Unit) = {
    import s._
    import symbols.{given, _}

    // Represents a substitution to a new function, along with parameter and type parameter mappings
    case class FunSubst(
      fd: FunDef,
      paramsMap: Map[ValDef, ValDef],
      tparamsMap: Map[TypeParameter, TypeParameter]
    )

    def isConditionAsRefinement(vd: ValDef): Boolean = vd.tpe match {
      case RefinementType(param, _) if param.tpe == UnitType() && vd.id.name == "prop" => true
      case _ => false
    }

    // The functions that closing `fd` can make mutually recursive with a closed function: `fd`
    // itself and the functions nested in it.
    val enclosingFunctions: Set[Identifier] = exprOps.collect[Identifier] {
      case LetRec(fds, _) => fds.map(_.id).toSet
      case _ => Set.empty
    } (fd.fullBody) + fd.id

    def callsEnclosingFunction(e: Expr): Boolean = exprOps.exists {
      case fi: FunctionInvocation => enclosingFunctions(fi.id)
      case app: ApplyLetRec => enclosingFunctions(app.id)
      case _ => false
    } (e)

    // Keep captured variables ordered by their lexical definition in `fd`.
    // This is important because types of later vars may depend on earlier ones.
    lazy val definitionOrder: Map[Identifier, Int] = {
      val order = scala.collection.mutable.LinkedHashMap.empty[Identifier, Int]
      def record(vd: ValDef): Unit = {
        if (!order.contains(vd.id)) order += (vd.id -> order.size)
      }

      fd.params.foreach(record)
      exprOps.preTraversal {
        case Let(vd, _, _) => record(vd)
        case Lambda(args, _) => args.foreach(record)
        case _ =>
      }(fd.fullBody)

      order.toMap
    }

    def closeFd(inner: LocalFunDef, outer: FunDef, free: Seq[RefinementVar[ValDef]]): FunSubst = {
      val LocalFunDef(id, tparams, params, returnType, fullBody, flags) = inner

      val tpFresh = outer.tparams map { _.freshen }
      val tparamsMap = outer.typeArgs.zip(tpFresh map {_.tp}).toMap

      val inst = new typeOps.TypeInstantiator(tparamsMap)

      // A captured binding with a definition becomes a binding of the closed function's body
      // instead of a parameter. The types of the parameters after it refer to its definition, while
      // the definitions of later bindings refer to the binding itself.
      val (paramSubst, _, freshVals, bindings) = (free ++ params.map((_, (tpe: Type, tparamsMap: Map[s.TypeParameter, s.Type]) => tpe, None)))
        .foldLeft((Map[ValDef, Expr](), Map[ValDef, Expr](), Seq[(ValDef, ValDef)](), Seq[(ValDef, Expr)]())) {
          case ((paramSubst, bindingSubst, vals, bindings), (vdOld, refine, definition)) =>
            val vd = vdOld.copy(tpe = typeOps.instantiateType(vdOld.tpe, tparamsMap))
            val refined = refine(vd.tpe, tparamsMap)
            val nvd = ValDef(vd.id.freshen, typeOps.replaceFromSymbols(paramSubst, refined), vd.flags).copiedFrom(vd)
            definition match {
              case Some(e) =>
                val instantiated = typeOps.instantiateType(e, tparamsMap)
                val inParams = exprOps.replaceFromSymbols(paramSubst, instantiated)
                val inBody = exprOps.replaceFromSymbols(bindingSubst, instantiated)
                // The binding's own type may refer to earlier bindings, which are in scope
                val bvd = nvd.copy(tpe = typeOps.replaceFromSymbols(bindingSubst, refined))
                (paramSubst + (vd -> inParams), bindingSubst + (vd -> bvd.toVariable), vals :+ (vdOld -> bvd), bindings :+ (bvd -> inBody))
              case None =>
                (paramSubst + (vd -> nvd.toVariable), bindingSubst + (vd -> nvd.toVariable), vals :+ (vdOld -> nvd), bindings)
            }
        }

      val freeMap = freshVals.toMap
      val boundVals = bindings.map(_._1).toSet
      val freshParams = freshVals.map(_._2).filterNot(boundVals)

      object bodyTransformer extends ConcreteStainlessSelfTreeTransformer {
        override def transform(e: Expr): Expr = e match {
          case v: Variable if freeMap.contains(v.toVal) =>
            freeMap(v.toVal).toVariable.copiedFrom(v)

          case let @ Let(id, v, r) if freeMap.contains(id) =>
            Let(freeMap(id), transform(v), transform(r)).copiedFrom(let)

          case app @ ApplyLetRec(id, tparams, tpe, tps, args) if id == inner.id =>
            val ntps = tps.map(transform) ++ tpFresh.map(_.tp)
            val nargs = freshParams.dropRight(args.length).map(_.toVariable) ++ args.map(transform)
            FunctionInvocation(id, ntps, nargs).copiedFrom(app)

          case _ => super.transform(e)
        }

        override def transform(tpe: Type): Type = tpe match {
          case tp: TypeParameter =>
            tparamsMap.getOrElse(tp, super.transform(tpe))

          case _ => super.transform(tpe)
        }
      }

      // The bindings are added after freshening, as calls in the body refer to them. They don't
      // generate verification conditions, which the outer function already has.
      val newBody = bindings.foldRight(exprOps.freshenLocals(bodyTransformer.transform(fullBody))) {
        case ((vd, e), body) => Let(vd, annotated(e, DropVCs), body).copiedFrom(body)
      }

      val newFd = new s.FunDef(
        id,
        tparams ++ tpFresh,
        freshParams,
        typeOps.replaceFromSymbols(paramSubst, inst.transform(returnType)),
        newBody,
        (flags :+ Derived(Some(outer.id))).distinct
      ).copiedFrom(inner)

      FunSubst(newFd, freeMap, tparamsMap)
    }

    /** Takes a FunDef and returns a Seq of all internal FunDef's contained in fd in closed form
     * (and fd itself, without inned FunDef's).
     *
     * The strategy is as follows: Remove one layer of nested FunDef's, then call
     * close recursively on the new functions.
     */
    def close(fd: FunDef): Seq[t.FunDef] = {

      // Directly nested functions with their p.c.
      val nestedWithPathsFull = {
        val funDefs = exprOps.directlyNestedFunDefs(fd.fullBody)
        collectWithPC(fd.fullBody) {
          case (LetRec(fd1, body), path) => (fd1.filter(funDefs), path)
        }
      }

      val nestedWithPaths: Map[LocalFunDef, Path] = (for((fds, path) <- nestedWithPathsFull; fd <- fds) yield (fd, path)).toMap
      val nestedFuns = nestedWithPaths.keys.toSeq
      val nestedFunsIds = nestedFuns.map(_.id).toSet
      // Collect all functions defined within lambdas
      val nfDefInLam = exprOps.collect {
        case l: Lambda => exprOps.collect {
          case LetRec(fds, _) => fds.map(_.id).toSet
          case _ => Set.empty
        } (l.body)
        case _ => Set.empty
      } (fd.fullBody)
      val nfDefOutsideLam = nestedFunsIds -- nfDefInLam

      // Transitively called functions from each function
      val callGraph: Map[Identifier, Set[Identifier]] = inox.utils.GraphOps.transitiveClosure(
        nestedFuns.map { f =>
          val calls = exprOps.innerFunctionCalls(f.fullBody) intersect nestedFunsIds
          // Collect all calls that also appear in the PC, but exclude those that calls functions that are defined within lambdas
          // because these cannot be called without calling the lambdas.
          val pcCalls = exprOps.innerFunctionCalls(nestedWithPaths(f).fullClause) intersect nfDefOutsideLam
          f.id -> (calls ++ pcCalls)
        }.toMap
      )

      val outerParams = fd.params

      // All free variables one should include, plus a PC filtered from unnecessary elements.
      // Contains free vars of the function itself plus of all transitively called functions.
      // Also contains free vars from PC if the PC is relevant to the fundef.
      // Also contains the open and closed vars of the PC, these will be filtered out at some
      // later point when computing the relevant arguments (see `closeFd`).
      val transFree: Map[Identifier, Seq[RefinementVar[Variable]]] = {
        def step(current: Map[Identifier, Set[Variable]]): Map[Identifier, Set[Variable]] = {
          nestedFuns.map { fd =>
            val transFreeVars = (callGraph(fd.id) + fd.id).flatMap(current)
            val fdFreeVars = fd.freeVariables
            // This fns + the other fns FVs, taking into account the variables appearing in their type as well
            val fdsFreeVars = (transFreeVars ++ fdFreeVars)
              .flatMap(v => Set(v) ++ typeOps.variablesOf(v.tpe))

            // Take all variables (free + bound) of PC that are relevant to the fns FVs.
            // For this fixpoint computation, we will consider PC-bound variable as free
            // (these will be removed once the fixpoint is reached, before "returning" from transFreeWithBindings).
            //
            // For example, in:
            //   def outer(x: BigInt, y: BigInt, z: BigInt) = {
            //     require(0 <= x && x <= y)
            //     require(z >= 42)
            //     val a = x + 1
            //     val b = a
            //     def inner1 = { val aa = a + 1 }
            //     def inner2 = { val yy = y }
            //   }
            // -inner1: `a` appears free , which will also pull in `x` into the computed FVs.
            // We then remove (just before returning from transFreeWithBindings) `a` from the set of FVs
            // and only keep `x`, which will be added as a parameter to `inner1`.
            // -inner2: `y` appears free, so it will be captured as well. `y` also appears
            // in a PC condition x <= y. We could drop this condition, but we chose here to capture `x`
            // as well in order to have 0 <= x && x <= y available in the hoisted version of `inner2`.
            // (a more sophisticated approach would be to eliminate `x` entirely and have 0 <= y instead).
            val path = nestedWithPaths(fd)
            val picked = path.elements.toSet.flatMap {
              case Path.CloseBound(vd, e) if fdsFreeVars.contains(vd.toVariable) =>
                // Take all FVs of `e` so that we can "reconstruct" `vd` from them in `closeFd`
                // (note that this `vd` is already picked because it appears in `fdsFreeVars`).
                exprOps.variablesOf(e)
              case Path.CloseBound(vd, e) if exprOps.variablesOf(e).intersect(fdsFreeVars).nonEmpty =>
                // `vd` may occur in a constraint somewhere, which can also transitively constrain the FVs
                Set(vd.toVariable)
              case Path.Condition(cond) =>
                val varsCond = exprOps.variablesOf(cond)
                if (varsCond.intersect(fdsFreeVars).nonEmpty) varsCond
                else Set.empty[Variable]
              case _ => Set.empty[Variable]
            }

            val pickedFromParams = outerParams.collect {
              case vd if typeOps.variablesOf(vd.tpe).intersect(fdsFreeVars).nonEmpty => 
                // similarly to binds and conditions on the path input args may have relevant constrainst in refinements
                vd.toVariable
            }

            (fd.id, fdsFreeVars ++ picked ++ pickedFromParams)
          }.toMap
        }

        val init = nestedFuns.map(fd => (fd.id, fd.freeVariables)).toMap
        val fix = inox.utils.fixpoint(step)(init)
        fix.map {
          case (fid, allVars) =>
            // We filter out the PC-bound variables in `allVars`, since these can be reconstructed using their definition
            // (which `closeFd` will do). We also remove path elements that are irrelevant to this fn.
            val path = nestedWithPaths.find(_._1.id == fid).get._2
            val boundVars = path.bindings.map(_._1.toVariable).toSet

            // We annotate outer path conditions with `DropConjunct` so that they are not checked when
            // calling the inner function (as we know they already hold at this point).
            // And we annotated bound expressions and path conditions with `DropVCs` so that they
            // don't generate verification conditions (e.g. index within bounds), as these would be
            // already checked in the outer function.
            val fromPath: Seq[RefinementVar[Variable]] = path.elements.collect {
              case Path.CloseBound(vd, e) if allVars.contains(vd.toVariable) => 
                // A captured binding is bound again to its definition in the closed function rather
                // than passed with an equality to it, which `--function-equality=none` rejects for
                // values that contain functions. When the definition calls an enclosing function, the
                // closed function would call it too and become mutually recursive with it, so the
                // binding is passed as is.
                val definition = if (callsEnclosingFunction(e)) None else Some(e)
                (vd.toVariable, (tpe: Type, _: Map[s.TypeParameter, s.Type]) => tpe, definition)
              case Path.Condition(cond) if exprOps.variablesOf(cond).intersect(allVars.toSet).nonEmpty => 
                val v = ValDef(FreshIdentifier("prop"), UnitType())
                (v.toVariable, (tpe: Type, tparamsMap: Map[s.TypeParameter, s.Type]) => {
                  val param = ValDef(FreshIdentifier("param"), tpe)
                  RefinementType(param, Annotated(typeOps.instantiateType(cond, tparamsMap), Seq(DropVCs, DropConjunct)))
                }, None)
            }
            val filteredVars: Seq[RefinementVar[Variable]] = allVars
              .filterNot(boundVars).toSeq
              .sortBy(v => definitionOrder.getOrElse(v.id, v.id.globalId))
              .map(v => (v, (tpe: Type, tparamsMap: Map[s.TypeParameter, s.Type]) => tpe, None))
            fid -> (filteredVars ++ fromPath)
        }
      }

      // Closed functions along with a map (old var -> new var).
      val closed = nestedFuns.map { inner =>
        inner.id -> closeFd(inner, fd, transFree(inner.id).map { case (v, refine, definition) => (v.toVal, refine, definition) })
      }.toMap

      class ClosingTransformer(override val s: self.s.type,
                               override val t: ast.Trees,
                               val subst: FunSubst)
        extends transformers.ConcreteTreeTransformer(s, t) {
        val FunSubst(_, callerMap, callerTMap) = subst

        override def transform(e: s.Expr): t.Expr = e match {
          case app @ ApplyLetRec(id, tparams, tpe, tps, args) if closed contains id =>

            val FunSubst(newCallee, calleeMap, calleeTMap) = closed(id)

            // This needs some explanation.
            // Say we have caller and callee. First we find the param. substitutions of callee
            // (say old -> calleeNew) and reverse them. So we have a mapping (calleeNew -> old).
            // We also have the caller mapping, (old -> callerNew).
            // So we pass the callee parameters through these two mappings to get the caller parameters.

            val tReverse = calleeTMap map { _.swap }
            val tOrigExtraOrdered = newCallee.tparams.map(_.tp).drop(tparams.size).map(tReverse)
            val tFinalExtra: Seq[TypeParameter] = tOrigExtraOrdered.map(tp => callerTMap(tp))
            val tparamsMap = (newCallee.tparams.map(_.tp).drop(tparams.size) zip tFinalExtra).toMap

            val mapReverse = calleeMap map { _.swap }
            val extraArgs = newCallee.params.dropRight(args.size).map { vd =>
              if isConditionAsRefinement(vd) then UnitLiteral()
              else typeOps.instantiateType(callerMap(mapReverse(vd)).toVariable, tparamsMap) 
            }

            t.FunctionInvocation(
              newCallee.id,
              tps.map(transform) ++ tFinalExtra.map(transform),
              extraArgs.map(transform) ++ args.map(transform)
            ).copiedFrom(app)

          case _ => super.transform(e)
        }
      }

      // A dummy substitution for fd, saying we should not change parameters
      val dummySubst = FunSubst(
        fd,
        Map.empty.withDefault(id => id),
        Map.empty.withDefault(id => id)
      )

      val closingSubst = FunSubst(fd, Map.empty.withDefault(id => id), Map.empty.withDefault(id => id))
      class Closing(override val t: self.t.type) extends ClosingTransformer(self.s, t, closingSubst) { closingSelf =>
        override def transform(e: closingSelf.s.Expr): closingSelf.t.Expr = e match {
          case closingSelf.s.LetRec(_, bd) => transform(bd)
          case _ => super.transform(e)
        }
      }
      val closing = new Closing(self.t)
      val newFd = closing.transform(fd)

      class ClosedFd(override val t: self.s.type, override val subst: FunSubst) extends ClosingTransformer(self.s, t, subst)
      val closedFds = closed.values.toList.map {
        case fs @ FunSubst(fd, _, _) =>
          val tr = new ClosedFd(self.s, fs)
          val transformedParams = fd.params.map(vd => vd.copy(tpe = tr.transform(vd.tpe)))
          fd.copy(
            params = transformedParams,
            returnType = tr.transform(fd.returnType),
            fullBody = tr.transform(fd.fullBody)
          )
      }

      // Recursively close new functions
      newFd +: closedFds.flatMap(close)
    }

    (close(fd), ())
  }
}

object FunctionClosure {
  def apply(ts: Trees, tt: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends FunctionClosure(s, t)
    new Impl(ts, tt)
  }
}
