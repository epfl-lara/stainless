/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait FunctionClosure
  extends CachingPhase
     with SimplyCachedFunctions
     with IdentitySorts { self =>

  val s: Trees
  val t: ast.Trees

  override protected type FunctionResult = Seq[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): Seq[t.FunDef] = {
    import s._
    import symbols._

    // Represents a substitution to a new function, along with parameter and type parameter
    // mappings
    case class FunSubst(
      fd: FunDef,
      paramsMap: Map[ValDef, ValDef],
      tparamsMap: Map[TypeParameter, TypeParameter]
    )

    def filterByIds(path: Path, ids: Set[Identifier]): Path = {
      def containsIds(e: Expr): Boolean = exprOps.exists {
        case Variable(id, _, _) => ids contains id
        case _ => false
      }(e)

      import Path._
      path.elements.foldLeft(Path.empty) {
        case (pc, CloseBound(vd, e)) if (ids contains vd.id) || containsIds(e) => pc withBinding (vd -> e)
        case (pc, Condition(cond)) if containsIds(cond) => pc withCond cond
        case (pc, _) => pc
      }
    }

    def closeFd(inner: LocalFunDef, outer: FunDef, pc: Path, free: Seq[ValDef]): FunSubst = {
      val LocalFunDef(name, tparams, Lambda(args, body)) = inner

      val reqPC = filterByIds(pc, free.map(_.id).toSet)

      val tpFresh = outer.tparams map { _.freshen }
      val tparamsMap = outer.typeArgs.zip(tpFresh map {_.tp}).toMap

      val inst = new typeOps.TypeInstantiator(tparamsMap)
      val freshVals = (args ++ free).map { vd =>
        val tvd = inst.transform(vd)
        tvd -> tvd.freshen
      }

      val freeMap = freshVals.toMap
      val freshParams = freshVals.filterNot(p => reqPC.bindings exists (_._1.id == p._1.id)).map(_._2)

      val instBody = inst.transform(withPath(body, reqPC))

      val fullBody = exprOps.preMap {
        case v: Variable => freeMap.get(v.toVal).map(_.toVariable.copiedFrom(v))

        case let @ Let(id, v, r) if freeMap.isDefinedAt(id) =>
          Some(Let(freeMap(id), v, r).copiedFrom(let))

        case app @ ApplyLetRec(v @ Variable(id, FunctionType(from, to), _), tparams, tps, args) if v == name =>
          val ntps = tps ++ tpFresh.map(_.tp)
          val nargs = args ++ freshParams.drop(args.length).map(_.toVariable)
          Some(FunctionInvocation(id, ntps, nargs).copiedFrom(app))

        case _ => None
      }(instBody)

      val newFd = new s.FunDef(
        name.id,
        tparams ++ tpFresh,
        freshParams,
        inst.transform(name.tpe.asInstanceOf[FunctionType].to),
        fullBody,
        (name.flags ++ outer.flags :+ Derived(outer.id)).distinct
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
      val nestedFunsIds = nestedFuns.map(_.name.id).toSet

      // Transitively called functions from each function
      val callGraph: Map[Identifier, Set[Identifier]] = inox.utils.GraphOps.transitiveClosure(
        nestedFuns.map { f =>
          val calls = exprOps.innerFunctionCalls(f.body) intersect nestedFunsIds
          val pcCalls = exprOps.innerFunctionCalls(nestedWithPaths(f).fullClause) intersect nestedFunsIds
          f.name.id -> (calls ++ pcCalls)
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
            val transFreeVars = (callGraph(fd.name.id) + fd.name.id).flatMap(current)
            val reqPath = filterByIds(nestedWithPaths(fd), transFreeVars.map(_.id))
            (fd.name.id, transFreeVars ++ exprOps.variablesOf(fd.body) ++ reqPath.freeVariables)
          }.toMap
        }

        val init = nestedFuns.map(fd => (fd.name.id, exprOps.variablesOf(fd.body))).toMap
        inox.utils.fixpoint(step)(init)
      }

      val transFree: Map[Identifier, Seq[Variable]] = 
        //transFreeWithBindings.map(p => (p._1, p._2 -- nestedWithPaths(p._1).bindings.map(_._1))).map(p => (p._1, p._2.toSeq))
        transFreeWithBindings.map(p => (p._1, p._2.toSeq.sortBy(_.id.name)))

      // Closed functions along with a map (old var -> new var).
      val closed = nestedWithPaths.map {
        case (inner, pc) => inner.name.id -> closeFd(inner, fd, pc, transFree(inner.name.id).map(_.toVal))
      }

      trait ClosingTransformer extends ast.TreeTransformer {
        val s: self.s.type = self.s
        val subst: FunSubst

        lazy val FunSubst(_, callerMap, callerTMap) = subst

        override def transform(e: s.Expr): t.Expr = e match {
          case app @ ApplyLetRec(fun, tparams, tps, args) if closed contains fun.id =>
            val FunSubst(newCallee, calleeMap, calleeTMap) = closed(fun.id)

            // This needs some explanation.
            // Say we have caller and callee. First we find the param. substitutions of callee
            // (say old -> calleeNew) and reverse them. So we have a mapping (calleeNew -> old).
            // We also have the caller mapping, (old -> callerNew).
            // So we pass the callee parameters through these two mappings to get the caller parameters.

            val tReverse = calleeTMap map { _.swap }
            val tOrigExtraOrdered = newCallee.tparams.map{_.tp}.drop(tparams.size).map(tReverse)
            val tFinalExtra: Seq[TypeParameter] = tOrigExtraOrdered.map(tp => callerTMap(tp))
            val tparamsMap = (newCallee.tparams.map(_.tp).drop(tparams.size) zip tFinalExtra).toMap

            val mapReverse = calleeMap map { _.swap }
            val extraArgs = newCallee.params.drop(args.size).map { vd =>
              typeOps.instantiateType(callerMap(mapReverse(vd)).toVariable, tparamsMap)
            }

            t.FunctionInvocation(
              newCallee.id,
              tps.map(transform) ++ tFinalExtra.map(transform),
              args.map(transform) ++ extraArgs.map(transform)
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

      object closing extends ClosingTransformer {
        val t: self.t.type = self.t
        val subst = FunSubst(fd, Map.empty.withDefault(id => id), Map.empty.withDefault(id => id))

        override def transform(e: s.Expr): t.Expr = e match {
          case s.LetRec(_, bd) => transform(bd)
          case _ => super.transform(e)
        }
      }

      val newFd = closing.transform(fd)

      val closedFds = closed.values.toList.map { case fs @ FunSubst(fd, _, _) =>
        fd.copy(fullBody = new ClosingTransformer {
          val t: self.s.type = self.s
          val subst = fs
        }.transform(fd.fullBody))
      }

      // Recursively close new functions
      newFd +: closedFds.flatMap(close)
    }

    close(fd)
  }
}

object FunctionClosure {
  def apply(ts: Trees, tt: inlining.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new FunctionClosure {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
