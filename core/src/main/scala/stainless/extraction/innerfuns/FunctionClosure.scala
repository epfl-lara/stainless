/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait FunctionClosure extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: inlining.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._

    // Represents a substitution to a new function, along with parameter and type parameter
    // mappings
    case class FunSubst(
      fd: FunDef,
      paramsMap: Map[ValDef, ValDef],
      tparamsMap: Map[TypeParameter, TypeParameter]
    )

    def closeFd(inner: LocalFunDef, outer: FunDef, pc: Path, free: Seq[ValDef]): FunSubst = {
      val LocalFunDef(name, tparams, Lambda(args, body)) = inner

      //println("inner: " + inner)
      //println("pc: " + pc)
      //println("free: " + free.map(_.uniqueName))

      val reqPC = pc.filterByIds(free.map(_.id).toSet)

      val tpFresh = outer.tparams map { _.freshen }
      val tparamsMap = outer.typeArgs.zip(tpFresh map {_.tp}).toMap

      val freshVals = (args ++ free).map { vd =>
        val tvd = vd.copy(tpe = instantiateType(vd.tpe, tparamsMap))
        tvd -> tvd.freshen
      }

      val freeMap = freshVals.toMap
      val freshParams = freshVals.filterNot(p => reqPC.isBound(p._1.id)).map(_._2)

      val instBody = instantiateType(withPath(body, reqPC), tparamsMap)

      val fullBody = exprOps.preMap {
        case v: Variable => freeMap.get(v.toVal).map(_.toVariable)

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
        instantiateType(name.tpe.asInstanceOf[FunctionType].to, tparamsMap),
        fullBody,
        name.flags ++ outer.flags + Derived(outer.id)
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
        transformers.CollectorWithPC(s)(symbols) {
          case (LetRec(fd1, body), path) => (fd1.filter(funDefs), path)
        }.collect(fd.fullBody)
      }

      val nestedWithPaths = (for((fds, path) <- nestedWithPathsFull; fd <- fds) yield (fd, path)).toMap
      val nestedFuns = nestedWithPaths.keys.toSeq
      val nestedFunsIds = nestedFuns.map(_.name.id).toSet

      // Transitively called funcions from each function
      val callGraph: Map[Identifier, Set[Identifier]] = inox.utils.GraphOps.transitiveClosure(
        nestedFuns.map { f =>
          val calls = exprOps.innerFunctionCalls(f.body) intersect nestedFunsIds
          val pcCalls = exprOps.innerFunctionCalls(nestedWithPaths(f).fullClause) intersect nestedFunsIds
          f.name.id -> (calls ++ pcCalls)
        }.toMap
      )
      //println("nested funs: " + nestedFuns)
      //println("call graph: " + callGraph)

      def freeVars(fd: LocalFunDef, pc: Path): Set[Variable] =
        exprOps.variablesOf(fd.body) ++ pc.variables ++ pc.bindings.map(_._1.toVariable)

      // All free variables one should include.
      // Contains free vars of the function itself plus of all transitively called functions.
      // also contains free vars from PC if the PC is relevant to the fundef
      val transFreeWithBindings: Map[Identifier, Set[Variable]] = {
        def step(current: Map[Identifier, Set[Variable]]): Map[Identifier, Set[Variable]] = {
          nestedFuns.map { fd =>
            val transFreeVars = (callGraph(fd.name.id) + fd.name.id).flatMap(current)
            val reqPath = nestedWithPaths(fd).filterByIds(transFreeVars.map(_.id))
            (fd.name.id, transFreeVars ++ freeVars(fd, reqPath))
          }.toMap
        }

        val init = nestedFuns.map(fd => (fd.name.id, exprOps.variablesOf(fd.body))).toMap
        inox.utils.fixpoint(step)(init)
      }

      val transFree: Map[Identifier, Seq[Variable]] = 
        //transFreeWithBindings.map(p => (p._1, p._2 -- nestedWithPaths(p._1).bindings.map(_._1))).map(p => (p._1, p._2.toSeq))
        transFreeWithBindings.map(p => (p._1, p._2.toSeq))

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
              instantiateType(callerMap(mapReverse(vd)).toVariable, tparamsMap)
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

    // For ADT transformation
    object identity extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    t.NoSymbols
      .withFunctions(symbols.functions.values.toSeq.flatMap(close))
      .withADTs(symbols.adts.values.toSeq.map(identity.transform))
  }
}
