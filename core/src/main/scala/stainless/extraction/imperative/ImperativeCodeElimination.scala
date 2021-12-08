/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

class ImperativeCodeElimination(override val s: Trees)(override val t: s.type)
                               (using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleFunctions
     with IdentitySorts
     with oo.IdentityClasses
     with oo.IdentityTypeDefs
     with SimplyCachedFunctions
     with SimplyCachedSorts
     with oo.SimplyCachedClasses {
  import s._

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): t.FunDef = {
    import symbols.{given, _}
    import exprOps._
    import exprOps.{ replaceKeepPositions => replace }

    /* varsInScope refers to variable declared in the same level scope.
     * Typically, when entering a nested function body, the scope should be
     * reset to empty */
    case class State(
      parent: FunDef,
      varsInScope: Set[Variable],
      localsMapping: Map[Identifier, (LocalFunDef, Seq[Variable])]
    ) {
      def withVar(vd: ValDef) = copy(varsInScope = varsInScope + vd.toVariable)
      def withLocal(id: Identifier, fd: LocalFunDef, vars: Seq[Variable]) =
        copy(localsMapping = localsMapping + (id -> (fd, vars)))
    }

    //return a "scope" consisting of purely functional code that defines potentially needed
    //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
    //to their new name defined in the scope. The first returned valued is the value of the expression
    //that should be introduced as such in the returned scope (the val already refers to the new names)
    def toFunction(expr: Expr)(using state: State): (Expr, Expr => Expr, Map[Variable, Variable]) = {
      import state._

      val (res, scope, fun): (Expr, Expr => Expr, Map[Variable, Variable]) = expr match {
        case LetVar(vd, e, b) =>
          val newVd = vd.freshen
          val (rhsVal, rhsScope, rhsFun) = toFunction(e)
          val (bodyRes, bodyScope, bodyFun) = toFunction(b)(using state.withVar(vd))
          val newSubst = rhsFun + (vd.toVariable -> newVd.toVariable)
          val scope = (body: Expr) => rhsScope(Let(newVd, rhsVal, replaceFromSymbols(newSubst, bodyScope(body))).copiedFrom(expr))
          (bodyRes, scope, newSubst ++ bodyFun)

        case Assignment(v, e) =>
          assert(varsInScope.contains(v), s"varsInScope should contain ${v.asString}")
          val newVd = v.toVal.freshen
          val (rhsVal, rhsScope, rhsFun) = toFunction(e)
          val scope = (body: Expr) => rhsScope(Let(newVd, rhsVal, body).copiedFrom(expr))
          (UnitLiteral(), scope, rhsFun + (v -> newVd.toVariable))

        case Snapshot(e) => toFunction(e)
        case FreshCopy(e) => toFunction(e)

        case ite @ IfExpr(cond, tExpr, eExpr) =>
          val (cRes, cScope, cFun) = toFunction(cond)
          val (tRes, tScope, tFun) = toFunction(tExpr)
          val (eRes, eScope, eFun) = toFunction(eExpr)

          val modifiedVars: Seq[Variable] = (tFun.keys ++ eFun.keys).toSet.intersect(varsInScope).toSeq
          val res = ValDef.fresh("res", ite.getType)
          val freshVars = modifiedVars.map(_.freshen)
          val iteType = tupleTypeWrap(res.tpe +: freshVars.map(_.tpe))

          val thenVal = tupleWrap(tRes +: modifiedVars.map(v => tFun.getOrElse(v, v)))
          val elseVal = tupleWrap(eRes +: modifiedVars.map(v => eFun.getOrElse(v, v)))
          val iteExpr = IfExpr(cRes, replaceFromSymbols(cFun, tScope(thenVal)), replaceFromSymbols(cFun, eScope(elseVal))).copiedFrom(ite)

          val scope = (body: Expr) => {
            val tupleVd = ValDef.fresh("t", iteType)
            cScope(Let(tupleVd, iteExpr, Let(
              res,
              tupleSelect(tupleVd.toVariable, 1, modifiedVars.nonEmpty),
              freshVars.zipWithIndex.foldLeft(body)((b, p) =>
                Let(p._1.toVal, tupleSelect(tupleVd.toVariable, p._2 + 2, true), b)
              ))
            ).copiedFrom(expr))
          }

          (res.toVariable, scope, cFun ++ (modifiedVars zip freshVars))

        case m @ MatchExpr(scrut, cses) =>
          val csesRhs = cses.map(_.rhs) //we can ignore pattern, and the guard is required to be pure
          val (csesRes, csesScope, csesFun) = csesRhs.map(toFunction).unzip3
          val (scrutRes, scrutScope, scrutFun) = toFunction(scrut)

          val modifiedVars: Seq[Variable] = csesFun.flatMap(_.keys).toSet.intersect(varsInScope).toSeq
          val res = ValDef.fresh("res", m.getType).setPos(m)
          val freshVars = modifiedVars.map(_.freshen)
          val matchType = tupleTypeWrap(res.tpe +: freshVars.map(_.tpe))

          val csesVals = csesRes.zip(csesFun).map {
            case (cRes, cFun) => tupleWrap(cRes +: modifiedVars.map(v => cFun.getOrElse(v, v)))
          }

          val newRhs = csesVals.zip(csesScope).map {
            case (cVal, cScope) => replace(scrutFun, cScope(cVal))
          }

          val matchE = MatchExpr(scrutRes, cses.zip(newRhs).map {
            case (mc @ MatchCase(pat, guard, _), newRhs) =>
              //guard need to update ids (substitution of new names, and new fundef)
              //but wont have side effects
              MatchCase(pat, guard.map { g =>
                val (resGuard, scopeGuard, _) = toFunction(g)
                replaceFromSymbols(scrutFun, scopeGuard(resGuard))
              }, newRhs).copiedFrom(mc)
          }).copiedFrom(m)

          val scope = (body: Expr) => {
            val tupleVd = ValDef.fresh("t", matchType)
            scrutScope(
              Let(tupleVd, matchE,
                Let(res, tupleSelect(tupleVd.toVariable, 1, freshVars.nonEmpty),
                  freshVars.zipWithIndex.foldLeft(body)((b, p) =>
                    Let(p._1.toVal, tupleSelect(tupleVd.toVariable, p._2 + 2, true), b)
                  )
                )
              )
            )
          }

          (res.toVariable, scope, scrutFun ++ (modifiedVars zip freshVars))

        case Block(Seq(), expr) =>
          toFunction(expr)

        case bl @ Block(exprs, expr) =>
          val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Variable, Variable]()) { (e, acc) =>
            val (accScope, accFun) = acc
            val (rVal, rScope, rFun) = toFunction(e)
            val scope = (body: Expr) =>
              rScope(
                replaceFromSymbols(
                  rFun,
                  Let(
                    ValDef.fresh("tmp", rVal.getType).copiedFrom(body),
                    rVal,
                    accScope(body)
                  ).copiedFrom(body)
                )
              )
            (scope, rFun ++ accFun)
          }

          val (lastRes, lastScope, lastFun) = toFunction(expr)
          val finalFun = fun ++ lastFun
          (
            replaceFromSymbols(finalFun, lastRes),
            (body: Expr) => scope(replaceFromSymbols(fun, lastScope(body)).setPos(expr)),
            finalFun
          )

        //pure expression (that could still contain side effects as a subexpression) (evaluation order is from left to right)
        case Let(vd, e, b) =>
          val (bindRes, bindScope, bindFun) = toFunction(e)
          val (bodyRes, bodyScope, bodyFun) = toFunction(b)
          (
            bodyRes,
            (b2: Expr) => bindScope(Let(vd, bindRes, replaceFromSymbols(bindFun, bodyScope(b2))).copiedFrom(expr)),
            bindFun ++ bodyFun
          )

        //a function invocation can update variables in scope.
        case alr @ ApplyLetRec(id, tparams, tpe, tps, args) if localsMapping contains id =>
          val (recArgs, argScope, argFun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Variable, Variable]())) { (arg, acc) =>
            val (accArgs, accScope, accFun) = acc
            val (argVal, argScope, argFun) = toFunction(arg)
            val newScope = (body: Expr) => argScope(replaceFromSymbols(argFun, accScope(body)))
            (argVal +: accArgs, newScope, argFun ++ accFun)
          }

          val (fd, modifiedVars) = localsMapping(id)
          val newReturnType = TupleType(tpe.to +: modifiedVars.map(_.getType))
          val newInvoc = ApplyLetRec(id, fd.tparams.map(_.tp),
            FunctionType(tpe.from ++ modifiedVars.map(_.getType), newReturnType).copiedFrom(tpe),
            tps, recArgs ++ modifiedVars
          ).setPos(alr)

          val freshVars = modifiedVars.map(_.freshen)
          val tmpTuple = ValDef.fresh("t", newInvoc.getType)

          val scope = (body: Expr) => {
            argScope(Let(tmpTuple, newInvoc,
              freshVars.zipWithIndex.foldRight(body) { case ((v, i), b) =>
                Let(v.toVal, TupleSelect(tmpTuple.toVariable, i + 2), b)
              }
            ))
          }

          (TupleSelect(tmpTuple.toVariable, 1), scope, argFun ++ (modifiedVars zip freshVars))

        case LetRec(Seq(fd), b) =>
          val inner = Inner(fd)
          // TODO(gsps): Migrate to new specs API
          val (specs, body) = deconstructSpecs(inner.fullBody)

          def fdWithoutSideEffects = {
            val newBody = body.map { bd =>
              val (fdRes, fdScope, _) = toFunction(bd)
              fdScope(fdRes)
            }
            val newFd = inner.copy(fullBody = reconstructSpecs(specs, newBody, inner.returnType))
            val (bodyRes, bodyScope, bodyFun) = toFunction(b)
            (bodyRes, (b2: Expr) => LetRec(Seq(newFd.toLocal), bodyScope(b2)).setPos(fd).copiedFrom(expr), bodyFun)
          }

          body match {
            case Some(bd) =>
              //we take any vars in scope needed (even for read only).
              //if read only, we only need to capture it without returning, but
              //returning it simplifies the code (more consistent) and should
              //not have a big impact on performance
              val modifiedVars: Seq[Variable] = {
                val freeVars = variablesOf(inner.fullBody)
                val transitiveVars = collect[Variable] {
                  case ApplyLetRec(id, _, _, _, _) =>
                    state.localsMapping.get(id).map(_._2.toSet).getOrElse(Set())
                  case _ => Set()
                } (inner.fullBody)

                (freeVars ++ transitiveVars).intersect(state.varsInScope).toSeq
              }

              //val modifiedVars: List[Identifier] =
              //  collect[Identifier]({
              //    case Assignment(v, _) => Set(v)
              //    case FunctionInvocation(tfd, _) => state.funDefsMapping.get(tfd.fd).map(p => p._2.toSet).getOrElse(Set())
              //    case _ => Set()
              //  })(bd).intersect(state.varsInScope).toList

              if (modifiedVars.isEmpty) fdWithoutSideEffects else {
                val freshVars: Seq[Variable] = modifiedVars.map(_.freshen)

                val newParams: Seq[ValDef] = inner.params ++ freshVars.map(_.toVal)
                val freshVarDecls: Seq[Variable] = freshVars.map(_.freshen)

                val rewritingMap: Map[Variable, Variable] = modifiedVars.zip(freshVarDecls).toMap
                val freshBody = postMap {
                  case Assignment(v, e) => rewritingMap.get(v).map(nv => Assignment(nv, e))
                  case v: Variable => rewritingMap.get(v)
                  case _ => None
                } (bd)

                val wrappedBody = freshVars.zip(freshVarDecls).foldLeft(freshBody) {
                  (body, p) => LetVar(p._2.toVal, p._1, body)
                }

                val (fdRes, fdScope, fdFun) = toFunction(wrappedBody)(using State(state.parent, Set(),
                  state.localsMapping.map { case (v, (fd, mvs)) =>
                    (v, (fd, mvs.map(v => rewritingMap.getOrElse(v, v))))
                  } + (fd.id -> ((fd, freshVarDecls)))
                ))

                val newRes = Tuple(fdRes +: freshVarDecls.map(fdFun))
                val newBody = fdScope(newRes)

                val newReturnType = TupleType(inner.returnType +: modifiedVars.map(_.tpe))

                val newSpecs = specs.map {
                  case Postcondition(post @ Lambda(Seq(res), postBody)) =>
                    val newRes = ValDef(res.id.freshen, newReturnType)

                    val newBody = replaceSingle(
                      (modifiedVars.zip(freshVars).map { case (ov, nv) => Old(ov) -> nv } ++
                      modifiedVars.zipWithIndex.map { case (v, i) =>
                        (v -> TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)
                      } :+ (res.toVariable -> TupleSelect(newRes.toVariable, 1))).toMap,
                      postBody
                    )

                    val (r, scope, _) = toFunction(newBody)
                    Postcondition(Lambda(Seq(newRes), scope(r)).setPos(post))

                  case spec => spec.transform { cond =>
                    val fresh = replaceFromSymbols((modifiedVars zip freshVars).toMap, cond)
                    //still apply recursively to update all function invocation
                    val (res, scope, _) = toFunction(fresh)
                    scope(res)
                  }
                }

                val newFd = inner.copy(
                  params = newParams,
                  fullBody = reconstructSpecs(newSpecs, Some(newBody), newReturnType),
                  returnType = newReturnType
                )

                val (bodyRes, bodyScope, bodyFun) = toFunction(b)(using state.withLocal(fd.id, fd, modifiedVars))
                (bodyRes, (b2: Expr) => LetRec(Seq(newFd.toLocal), bodyScope(b2)).copiedFrom(expr), bodyFun)
              }

            case None => fdWithoutSideEffects
          }

        //TODO: no support for true mutual recursion
        case LetRec(fds, b) =>
          if (fds.isEmpty)
            toFunction(b)
          else
            toFunction(LetRec(Seq(fds.head), LetRec(fds.tail, b)))

        //TODO: handle vars in scope, just like LetRec
        case ld @ Lambda(params, body) =>
          val (bodyVal, bodyScope, bodyFun) = toFunction(body)
          (Lambda(params, bodyScope(bodyVal)).copiedFrom(ld), (e: Expr) => e, Map())

        case f @ Forall(params, body) =>
          // Recall that Forall cannot mutate variables from the scope
          val (bodyVal, bodyScope, bodyFun) = toFunction(body)
          (Forall(params, bodyScope(bodyVal)).copiedFrom(f), (e: Expr) => e, Map())

        case c @ Choose(res, pred) =>
          //Recall that Choose cannot mutate variables from the scope
          val (predVal, predScope, predFun) = toFunction(pred)
          (Choose(res, predScope(predVal)).copiedFrom(c), (e: Expr) => e, Map())

        case and @ And(exprs) =>
          val results = exprs.map(toFunction)
          (
            And(results.map(r => r._2(r._1))).setPos(and),
            (e: Expr) => e,
            results.map(_._3).foldLeft(Map[Variable, Variable]())(_ ++ _)
          )

        case or @ Or(exprs) =>
          val results = exprs.map(toFunction)
          (
            Or(results.map(r => r._2(r._1))).setPos(or),
            (e: Expr) => e,
            results.map(_._3).foldLeft(Map[Variable, Variable]())(_ ++ _)
          )

        case i @ Implies(lhs, rhs) =>
          val (lVal, lScope, lFun) = toFunction(lhs)
          val (rVal, rScope, rFun) = toFunction(rhs)
          (Implies(lScope(lVal), rScope(rVal)).setPos(i), (e: Expr) => e, lFun ++ rFun)

        //TODO: this should be handled properly by the Operator case, but there seems to be a subtle bug in the way Let's are lifted
        //      which leads to Assert refering to the wrong value of a var in some cases.
        case a @ Assert(cond, msg, body) =>
          val (condVal, condScope, condFun) = toFunction(cond)
          val (bodyRes, bodyScope, bodyFun) = toFunction(body)
          val scope = (body: Expr) => condScope(Assert(condVal, msg, replaceFromSymbols(condFun, bodyScope(body))).copiedFrom(a))
          (bodyRes, scope, condFun ++ bodyFun)

        //TODO: same as the assert case
        case a @ Assume(cond, body) =>
          val (condVal, condScope, condFun) = toFunction(cond)
          val (bodyRes, bodyScope, bodyFun) = toFunction(body)
          val scope = (body: Expr) => condScope(Assume(condVal, replaceFromSymbols(condFun, bodyScope(body))).copiedFrom(a))
          (bodyRes, scope, condFun ++ bodyFun)

        case n @ Operator(args, recons) =>
          val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Variable, Variable]())) { (arg, acc) =>
            val (accArgs, accScope, accFun) = acc
            val (argVal, argScope, argFun) = toFunction(arg)
            val newScope = (body: Expr) => argScope(replaceFromSymbols(argFun, accScope(body)))
            (argVal +: accArgs, newScope, argFun ++ accFun)
          }
          (recons(recArgs).setPos(n), scope, fun)
      }

      (res.ensurePos(expr.getPos), scope, fun)
    }

    def requireRewriting(expr: Expr) = expr match {
      case (e: Block) => true
      case (e: Assignment) => true
      case (e: LetVar) => true
      case (e: Old) => true
      case (e: Snapshot) => true
      case (e: FreshCopy) => true
      case _ => false
    }

    if (exprOps.exists(requireRewriting)(fd.fullBody)) {
      def topLevelRewrite(expr: Expr): Expr = {
        val (res, scope, _) = toFunction(expr)(using State(fd, Set(), Map()))
        scope(res)
      }

      val specced = BodyWithSpecs(fd.fullBody)

      // NOTE: We assume that lets wrapping specs require no rewriting
      val newSpecced = specced.copy(
        specs = specced.specs.map {
          case Postcondition(ld @ Lambda(params, body)) =>
            // Remove `Old` trees for function parameters on which no effect occurred
            val newBody = replaceSingle(
              fd.params.map(vd => Old(vd.toVariable) -> vd.toVariable).toMap,
              body
            )
            Postcondition(Lambda(params, topLevelRewrite(newBody)).copiedFrom(ld))

          case spec => spec.transform(topLevelRewrite(_))
        },

        body = topLevelRewrite(specced.body)
      )

      fd.copy(fullBody = newSpecced.reconstructed)

    } else {
      fd
    }
  }
}

object ImperativeCodeElimination {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ImperativeCodeElimination(s)(t)
    new Impl(trees, trees)
  }
}
