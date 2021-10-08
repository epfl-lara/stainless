/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

class FunctionClosure(override val s: Trees, override  val t: ast.Trees)
                     (using override val context: inox.Context)
  extends CachingPhase
     with SimplyCachedFunctions
     with IdentitySorts { self =>

  override protected type FunctionResult = Seq[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): Seq[t.FunDef] = {
    import s._
    import symbols.{given, _}

    // Represents a substitution to a new function, along with parameter and type parameter mappings
    case class FunSubst(
      fd: FunDef,
      paramsMap: Map[ValDef, ValDef],
      tparamsMap: Map[TypeParameter, TypeParameter]
    )

    def closeFd(inner: LocalFunDef, outer: FunDef, pc: Path, free: Seq[ValDef]): FunSubst = {
      val LocalFunDef(id, tparams, params, returnType, fullBody, flags) = inner

      val tpFresh = outer.tparams map { _.freshen }
      val tparamsMap = outer.typeArgs.zip(tpFresh map {_.tp}).toMap

      val inst = new typeOps.TypeInstantiator(tparamsMap)

      val (paramSubst, freshVals) = (free ++ params)
        .foldLeft((Map[ValDef, Expr](), Seq[(ValDef, ValDef)]())) { case ((paramSubst, params), vdOld) =>
          val vd = vdOld.copy(tpe = typeOps.instantiateType(vdOld.tpe, tparamsMap))
          val ntpe = typeOps.replaceFromSymbols(paramSubst, vd.tpe)
          val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
          (paramSubst + (vd -> nvd.toVariable), params :+ (vdOld -> nvd))
        }

      val freeMap = freshVals.toMap
      val freshParams = freshVals.filterNot(p => pc.bindings exists (_._1.id == p._1.id)).map(_._2)

      // We annotate outer path conditions with `DropConjunct` so that they are not checked when
      // calling the inner function (as we know they already hold at this point).
      // And we annotated bound expressions and path conditions with `DropVCs` so that they
      // don't generate verification conditions (e.g. index within bounds), as these would be
      // already checked in the outer function.
      val oldBody = Path.fold[Expr](fullBody, {
        case (vd, e, acc) => Let(vd, annotated(e, DropVCs), acc).setPos(fullBody)
      }, {
        case (cond, Require(cond2, acc)) =>
          Require(SplitAnd(Annotated(cond, Seq(DropConjunct, DropVCs)).setPos(cond), cond2).setPos(cond), acc).setPos(fullBody)
        case (cond, acc) =>
          Require(Annotated(cond, Seq(DropConjunct, DropVCs)).setPos(cond), acc).setPos(fullBody)
      })(pc.elements)

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

      val newBody = exprOps.freshenLocals(bodyTransformer.transform(oldBody))

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

      val nestedWithPaths = (for((fds, path) <- nestedWithPathsFull; fd <- fds) yield (fd, path)).toMap
      val nestedFuns = nestedWithPaths.keys.toSeq
      val nestedFunsIds = nestedFuns.map(_.id).toSet

      // Transitively called functions from each function
      val callGraph: Map[Identifier, Set[Identifier]] = inox.utils.GraphOps.transitiveClosure(
        nestedFuns.map { f =>
          val calls = exprOps.innerFunctionCalls(f.fullBody) intersect nestedFunsIds
          val pcCalls = exprOps.innerFunctionCalls(nestedWithPaths(f).fullClause) intersect nestedFunsIds
          f.id -> (calls ++ pcCalls)
        }.toMap
      )

      // All free variables one should include.
      // Contains free vars of the function itself plus of all transitively called functions.
      // Also contains free vars from PC if the PC is relevant to the fundef.
      // Also contains the open and closed vars of the PC, these will be filtered out at some
      // later point when computing the relevant arguments (see `closeFd`).
      val transFreeWithBindings: Map[Identifier, Set[Variable]] = {
        def step(current: Map[Identifier, Set[Variable]]): Map[Identifier, Set[Variable]] = {
          nestedFuns.map { fd =>
            val transFreeVars = (callGraph(fd.id) + fd.id).flatMap(current)
            (fd.id, transFreeVars ++ fd.freeVariables ++ nestedWithPaths(fd).freeVariables)
          }.toMap
        }

        val init = nestedFuns.map(fd => (fd.id, fd.freeVariables)).toMap
        inox.utils.fixpoint(step)(init)
      }

      val transFree: Map[Identifier, Seq[Variable]] = 
        //transFreeWithBindings.map(p => (p._1, p._2 -- nestedWithPaths(p._1).bindings.map(_._1))).map(p => (p._1, p._2.toSeq))
        transFreeWithBindings.map(p => (p._1, p._2.toSeq.sortBy(_.id.name)))

      // Closed functions along with a map (old var -> new var).
      val closed = nestedWithPaths.map {
        case (inner, pc) => inner.id -> closeFd(inner, fd, pc, transFree(inner.id).map(_.toVal))
      }

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
              typeOps.instantiateType(callerMap(mapReverse(vd)).toVariable, tparamsMap)
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
          fd.copy(fullBody = new ClosedFd(self.s, fs).transform(fd.fullBody))
      }

      // Recursively close new functions
      newFd +: closedFds.flatMap(close)
    }

    close(fd)
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
