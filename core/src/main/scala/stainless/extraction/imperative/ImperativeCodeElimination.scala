/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait ImperativeCodeElimination extends inox.ast.SymbolTransformer {
  val trees: Trees
  lazy val s: trees.type = trees
  lazy val t: trees.type = trees
  import trees._

  def transform(syms: Symbols): Symbols = {
    import syms._
    import exprOps._

    /* varsInScope refers to variable declared in the same level scope.
     * Typically, when entering a nested function body, the scope should be
     * reset to empty */
    case class State(
      parent: FunDef,
      varsInScope: Set[Variable],
      localsMapping: Map[Variable, (Seq[TypeParameter], Seq[Variable])]
    ) {
      def withVar(vd: ValDef) = copy(varsInScope = varsInScope + vd.toVariable)
      def withLocal(v: Variable, tparams: Seq[TypeParameter], vars: Seq[Variable]) = 
        copy(localsMapping = localsMapping + (v -> (tparams, vars)))
    }

    //return a "scope" consisting of purely functional code that defines potentially needed 
    //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
    //to their new name defined in the scope. The first returned valued is the value of the expression
    //that should be introduced as such in the returned scope (the val already refers to the new names)
    def toFunction(expr: Expr)(implicit state: State): (Expr, Expr => Expr, Map[Variable, Variable]) = {
      import state._
      expr match {
        // Desugar Boolean bitwise operations &, | and ^; not actually tided to the overall transformation.
        case BoolBitwiseAnd(lhs, rhs) =>
          val l = ValDef(FreshIdentifier("lhs"), lhs.getType).copiedFrom(lhs)
          val r = ValDef(FreshIdentifier("rhs"), rhs.getType).copiedFrom(rhs)
          toFunction(
            Let(l, lhs,
              Let(r, rhs,
                And(l.toVariable, r.toVariable)))
          )

        case BoolBitwiseOr(lhs, rhs) =>
          val l = ValDef(FreshIdentifier("lhs"), lhs.getType).copiedFrom(lhs)
          val r = ValDef(FreshIdentifier("rhs"), rhs.getType).copiedFrom(rhs)
          toFunction(
            Let(l, lhs,
              Let(r, rhs,
                Or(l.toVariable, r.toVariable)))
          )

        case BoolBitwiseXor(lhs, rhs) =>
          val l = ValDef(FreshIdentifier("lhs"), lhs.getType).copiedFrom(lhs)
          val r = ValDef(FreshIdentifier("rhs"), rhs.getType).copiedFrom(rhs)
          toFunction(
            Let(l, lhs,
              Let(r, rhs,
                Not(Equals(l.toVariable, r.toVariable))))
          )

        case LetVar(vd, e, b) =>
          val newVd = vd.freshen
          val (rhsVal, rhsScope, rhsFun) = toFunction(e)
          val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withVar(vd))
          val newSubst = rhsFun + (vd.toVariable -> newVd.toVariable)
          val scope = (body: Expr) => rhsScope(Let(newVd, rhsVal, replaceFromSymbols(newSubst, bodyScope(body))).copiedFrom(expr))
          (bodyRes, scope, newSubst ++ bodyFun)

        case Assignment(v, e) =>
          assert(varsInScope.contains(v))
          val newVd = v.toVal.freshen
          val (rhsVal, rhsScope, rhsFun) = toFunction(e)
          val scope = (body: Expr) => rhsScope(Let(newVd, rhsVal, body).copiedFrom(expr))
          (UnitLiteral(), scope, rhsFun + (v -> newVd.toVariable))

        case ite @ IfExpr(cond, tExpr, eExpr) =>
          val (cRes, cScope, cFun) = toFunction(cond)
          val (tRes, tScope, tFun) = toFunction(tExpr)
          val (eRes, eScope, eFun) = toFunction(eExpr)

          val modifiedVars: Seq[Variable] = (tFun.keys ++ eFun.keys).toSet.intersect(varsInScope).toSeq
          val res = ValDef(FreshIdentifier("res"), ite.getType, Set.empty)
          val freshVars = modifiedVars.map(_.freshen)
          val iteType = tupleTypeWrap(res.tpe +: freshVars.map(_.tpe))

          val thenVal = tupleWrap(tRes +: modifiedVars.map(v => tFun.getOrElse(v, v)))
          val elseVal = tupleWrap(eRes +: modifiedVars.map(v => eFun.getOrElse(v, v)))
          val iteExpr = IfExpr(cRes, replaceFromSymbols(cFun, tScope(thenVal)), replaceFromSymbols(cFun, eScope(elseVal))).copiedFrom(ite)

          val scope = (body: Expr) => {
            val tupleVd = ValDef(FreshIdentifier("t"), iteType, Set.empty)
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
          val res = ValDef(FreshIdentifier("res"), m.getType, Set.empty)
          val freshVars = modifiedVars.map(_.freshen)
          val matchType = tupleTypeWrap(res.tpe +: freshVars.map(_.tpe))

          val csesVals = csesRes.zip(csesFun).map {
            case (cRes, cFun) => tupleWrap(cRes +: modifiedVars.map(v => cFun.getOrElse(v, v)))
          }

          val newRhs = csesVals.zip(csesScope).map {
            case (cVal, cScope) => replaceFromSymbols(scrutFun, cScope(cVal))
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
            val tupleVd = ValDef(FreshIdentifier("t"), matchType, Set.empty)
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

        case wh @ While(cond, body, optInv) =>
          val name = ValDef(
            FreshIdentifier(parent.id.name + "While").setPos(parent.id),
            FunctionType(Seq(), UnitType),
            Set.empty
          )

          val newBody = Some(IfExpr(cond,
            Block(Seq(body), ApplyLetRec(name.toVariable, Seq(), Seq(), Seq()).copiedFrom(wh)).copiedFrom(wh),
            UnitLiteral().copiedFrom(wh)).copiedFrom(wh))
          val newPost = Some(Lambda(
            Seq(ValDef(FreshIdentifier("bodyRes"), UnitType, Set.empty).copiedFrom(wh)),
            and(Not(getFunctionalResult(cond)).copiedFrom(cond), optInv.getOrElse(BooleanLiteral(true))).copiedFrom(wh)
          ).copiedFrom(wh))

          val fullBody = Lambda(Seq.empty, reconstructSpecs(optInv, newBody, newPost, UnitType)).copiedFrom(wh)
          val newExpr = LetRec(Seq(LocalFunDef(name, Seq(), fullBody)), ApplyLetRec(name.toVariable, Seq(), Seq(), Seq()).setPos(wh)).setPos(wh)
          toFunction(newExpr)

        case Block(Seq(), expr) =>
          toFunction(expr)

        case bl @ Block(exprs, expr) =>
          val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Variable, Variable]()) { (e, acc) =>
            val (accScope, accFun) = acc
            val (rVal, rScope, rFun) = toFunction(e)
            val scope = (body: Expr) => rVal match {
              case fi: FunctionInvocation =>
                rScope(replaceFromSymbols(rFun, Let(ValDef(FreshIdentifier("tmp"), fi.tfd.returnType, Set.empty).copiedFrom(body), rVal, accScope(body)).copiedFrom(body)))
              case alr: ApplyLetRec =>
                rScope(replaceFromSymbols(rFun, Let(ValDef(FreshIdentifier("tmp"), alr.getType, Set.empty).copiedFrom(body), rVal, accScope(body)).copiedFrom(body)))
              case _ =>
                rScope(replaceFromSymbols(rFun, accScope(body)))
            }
            (scope, rFun ++ accFun)
          }

          val (lastRes, lastScope, lastFun) = toFunction(expr)
          val finalFun = fun ++ lastFun
          (
            replaceFromSymbols(finalFun, lastRes),
            (body: Expr) => scope(replaceFromSymbols(fun, lastScope(body))),
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
        case alr @ ApplyLetRec(fun, tparams, tps, args) if localsMapping contains fun =>
          val (recArgs, argScope, argFun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Variable, Variable]())) { (arg, acc) =>
            val (accArgs, accScope, accFun) = acc
            val (argVal, argScope, argFun) = toFunction(arg)
            val newScope = (body: Expr) => argScope(replaceFromSymbols(argFun, accScope(body)))
            (argVal +: accArgs, newScope, argFun ++ accFun)
          }

          val (tparams, modifiedVars) = localsMapping(fun)
          val newReturnType = TupleType(fun.tpe.asInstanceOf[FunctionType].to +: modifiedVars.map(_.tpe))
          val newInvoc = ApplyLetRec(
            fun.copy(tpe = FunctionType(recArgs.map(_.getType) ++ modifiedVars.map(_.tpe), newReturnType)),
            tparams, tps, recArgs ++ modifiedVars
          ).setPos(alr)

          val freshVars = modifiedVars.map(_.freshen)
          val tmpTuple = ValDef(FreshIdentifier("t"), newInvoc.getType, Set.empty)

          val scope = (body: Expr) => {
            argScope(Let(tmpTuple, newInvoc,
              freshVars.zipWithIndex.foldRight(body) { case ((v, i), b) =>
                Let(v.toVal, (v, TupleSelect(tmpTuple.toVariable, i + 2)) match {
                  case (IsTyped(v, adt: ADTType), IsTyped(select, t2)) if v != t2 => AsInstanceOf(select, adt)
                  case (_, select) => select
                }, b)
              }
            ))
          }

          (TupleSelect(tmpTuple.toVariable, 1), scope, argFun ++ (modifiedVars zip freshVars))

        case LetRec(Seq(fd), b) =>
          val inner = Inner(fd)
          val (pre, body, post) = breakDownSpecs(inner.fullBody)

          def fdWithoutSideEffects = {
            val newBody = body.map { bd =>
              val (fdRes, fdScope, _) = toFunction(bd)
              fdScope(fdRes)
            }
            val newFd = inner.copy(fullBody = reconstructSpecs(pre, newBody, post, inner.returnType))
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
                  case ApplyLetRec(fun, _, _, _) => state.localsMapping.get(fun).map(p => p._2.toSet).getOrElse(Set())
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

                val (fdRes, fdScope, fdFun) = toFunction(wrappedBody)(State(state.parent, Set(),
                  state.localsMapping.map { case (v, (tparams, mvs)) =>
                    (v, (tparams, mvs.map(v => rewritingMap.getOrElse(v, v))))
                  } + (fd.name.toVariable -> ((fd.tparams.map(_.tp), freshVarDecls)))
                ))

                val newRes = Tuple(fdRes +: freshVarDecls.map(fdFun))
                val newBody = fdScope(newRes)

                val newReturnType = TupleType(inner.returnType +: modifiedVars.map(_.tpe))

                val newPre = pre.map { pre =>
                  val fresh = replaceFromSymbols((modifiedVars zip freshVars).toMap, pre)
                  //still apply recursively to update all function invocation
                  val (res, scope, _) = toFunction(fresh)
                  scope(res)
                }

                val newPost = post.map { post =>
                  val Lambda(Seq(res), postBody) = post
                  val newRes = ValDef(res.id.freshen, newReturnType, Set.empty)

                  val newBody = replaceSingle(
                    modifiedVars.zip(freshVars).map { case (ov, nv) => Old(ov) -> nv }.toMap ++
                    modifiedVars.zipWithIndex.map { case (v, i) => 
                      (v -> TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)
                    }.toMap + (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
                    postBody
                  )

                  val (r, scope, _) = toFunction(newBody)
                  Lambda(Seq(newRes), scope(r)).setPos(post)
                }

                val newFd = inner.copy(
                  params = newParams,
                  fullBody = reconstructSpecs(newPre, Some(newBody), newPost, newReturnType),
                  returnType = newReturnType
                )

                val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withLocal(fd.name.toVariable, fd.tparams.map(_.tp), modifiedVars))
                (bodyRes, (b2: Expr) => LetRec(Seq(newFd.toLocal), bodyScope(b2)).copiedFrom(expr), bodyFun)
              }

            case None => fdWithoutSideEffects
          }

        //TODO: no support for true mutual recursion
        case LetRec(fds, b) =>
          toFunction(LetRec(Seq(fds.head), LetRec(fds.tail, b)))

        //TODO: handle vars in scope, just like LetRec
        case ld @ Lambda(params, body) =>
          val (optPre, lBody) = body match {
            case Require(pred, body) => (Some(pred), body)
            case _ => (None, body)
          }
          val newPre = optPre.map { pre =>
            val (res, scope, _) = toFunction(pre)
            scope(res)
          }
          val (bodyVal, bodyScope, bodyFun) = toFunction(lBody)
          (Lambda(params, withPrecondition(bodyScope(bodyVal), newPre)).copiedFrom(ld), (e: Expr) => e, Map())

        case c @ Choose(res, pred) =>
          //Recall that Choose cannot mutate variables from the scope
          (c, (b2: Expr) => b2, Map())

        case And(args) =>
          val ifExpr = args.reduceRight((el, acc) => IfExpr(el, acc, BooleanLiteral(false)))
          toFunction(ifExpr)

        case Or(args) =>
          val ifExpr = args.reduceRight((el, acc) => IfExpr(el, BooleanLiteral(true), acc))
          toFunction(ifExpr)

        //TODO: this should be handled properly by the Operator case, but there seems to be a subtle bug in the way Let's are lifted
        //      which leads to Assert refering to the wrong value of a var in some cases.
        case a @ Assert(cond, msg, body) =>
          val (condVal, condScope, condFun) = toFunction(cond)
          val (bodyRes, bodyScope, bodyFun) = toFunction(body)
          val scope = (body: Expr) => condScope(Assert(condVal, msg, replaceFromSymbols(condFun, bodyScope(body))).copiedFrom(a))
          (bodyRes, scope, condFun ++ bodyFun)

        case n @ Operator(args, recons) =>
          val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Variable, Variable]())) { (arg, acc) =>
            val (accArgs, accScope, accFun) = acc
            val (argVal, argScope, argFun) = toFunction(arg)
            val newScope = (body: Expr) => argScope(replaceFromSymbols(argFun, accScope(body)))
            (argVal +: accArgs, newScope, argFun ++ accFun)
          }

          (recons(recArgs).copiedFrom(n), scope, fun)
      }
    }

    /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
    def getFunctionalResult(expr: Expr): Expr = postMap {
      case Block(_, res) => Some(res)
      case _ => None
    }(expr)

    def requireRewriting(expr: Expr) = expr match {
      case (e: Block) => true
      case (e: Assignment) => true
      case (e: While) => true
      case (e: LetVar) => true
      case _ => false
    }

    val newFds = for (fd <- syms.functions.values) yield {
      if (!exprOps.exists(requireRewriting)(fd.fullBody)) fd else {
        val (pre, body, post) = exprOps.breakDownSpecs(fd.fullBody)

        val newBody = body.map { body =>
          val (res, scope, _) = toFunction(body)(State(fd, Set(), Map()))
          scope(res)
        }

        //probably not the cleanest way to do it, but if somehow we still have Old
        //expressions at that point, they can be safely removed as the object is
        //equals to its original value
        val newPost = post.map(post => exprOps.postMap {
          case Old(e) => Some(e)
          case _ => None
        }(post).asInstanceOf[Lambda])

        fd.copy(fullBody = exprOps.reconstructSpecs(pre, newBody, newPost, fd.returnType))
      }
    }

    NoSymbols.withFunctions(newFds.toSeq).withADTs(syms.adts.values.toSeq)
  }
}
