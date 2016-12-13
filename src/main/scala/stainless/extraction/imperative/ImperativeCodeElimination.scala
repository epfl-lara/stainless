/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait ImperativeCodeElimination extends inox.ast.SymbolTransformer {
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    for {
      fd <- pgm.definedFunctions
      body <- fd.body if exists(requireRewriting)(body)
    } {
      val (res, scope, _) = toFunction(body)(State(fd, Set(), Map()))
      fd.body = Some(scope(res))

    }

    //probably not the cleanest way to do it, but if somehow we still have Old
    //expressions at that point, they can be safely removed as the object is
    //equals to its original value
    for {
      fd <- pgm.definedFunctions
    } {
      fd.postcondition = fd.postcondition.map(post => {
        preMap{
          case Old(v) => Some(v.toVariable)
          case _ => None
        }(post)
      })
    }

  }

  /* varsInScope refers to variable declared in the same level scope.
     Typically, when entering a nested function body, the scope should be
     reset to empty */
  private case class State(
    parent: FunDef, 
    varsInScope: Set[Identifier],
    funDefsMapping: Map[FunDef, (FunDef, List[Identifier])]
  ) {
    def withVar(i: Identifier) = copy(varsInScope = varsInScope + i)
    def withFunDef(fd: FunDef, nfd: FunDef, ids: List[Identifier]) = 
      copy(funDefsMapping = funDefsMapping + (fd -> (nfd, ids)))
  }

  //return a "scope" consisting of purely functional code that defines potentially needed 
  //new variables (val, not var) and a mapping for each modified variable (var, not val :) )
  //to their new name defined in the scope. The first returned valued is the value of the expression
  //that should be introduced as such in the returned scope (the val already refers to the new names)
  private def toFunction(expr: Expr)(implicit state: State): (Expr, Expr => Expr, Map[Identifier, Identifier]) = {
    import state._
    expr match {
      case LetVar(id, e, b) =>
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withVar(id))
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, replaceNames(rhsFun + (id -> newId), bodyScope(body))).copiedFrom(expr))
        (bodyRes, scope, (rhsFun + (id -> newId)) ++ bodyFun)
 
      case Assignment(id, e) =>
        assert(varsInScope.contains(id))
        val newId = id.freshen
        val (rhsVal, rhsScope, rhsFun) = toFunction(e)
        val scope = (body: Expr) => rhsScope(Let(newId, rhsVal, body).copiedFrom(expr))
        (UnitLiteral(), scope, rhsFun + (id -> newId))

      case ite@IfExpr(cond, tExpr, eExpr) =>
        val (cRes, cScope, cFun) = toFunction(cond)
        val (tRes, tScope, tFun) = toFunction(tExpr)
        val (eRes, eScope, eFun) = toFunction(eExpr)

        val iteRType = leastUpperBound(tRes.getType, eRes.getType).getOrElse(Untyped)

        val modifiedVars: Seq[Identifier] = (tFun.keys ++ eFun.keys).toSet.intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", iteRType)
        val freshIds = modifiedVars.map( _.freshen )
        val iteType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val thenVal = tupleWrap(tRes +: modifiedVars.map(vId => tFun.getOrElse(vId, vId).toVariable))
        val elseVal = tupleWrap(eRes +: modifiedVars.map(vId => eFun.getOrElse(vId, vId).toVariable))
        val iteExpr = IfExpr(cRes, replaceNames(cFun, tScope(thenVal)), replaceNames(cFun, eScope(elseVal))).copiedFrom(ite)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", iteType)
          cScope(Let(tupleId, iteExpr, Let(
            resId,
            tupleSelect(tupleId.toVariable, 1, modifiedVars.nonEmpty),
            freshIds.zipWithIndex.foldLeft(body)((b, id) =>
              Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
            ))
          ).copiedFrom(expr))
        }

        (resId.toVariable, scope, cFun ++ modifiedVars.zip(freshIds).toMap)

      case m @ MatchExpr(scrut, cses) =>
        val csesRhs = cses.map(_.rhs) //we can ignore pattern, and the guard is required to be pure
        val (csesRes, csesScope, csesFun) = csesRhs.map(toFunction).unzip3
        val (scrutRes, scrutScope, scrutFun) = toFunction(scrut)

        val modifiedVars: Seq[Identifier] = csesFun.toSet.flatMap((m: Map[Identifier, Identifier]) => m.keys).intersect(varsInScope).toSeq
        val resId = FreshIdentifier("res", m.getType)
        val freshIds = modifiedVars.map(id => FreshIdentifier(id.name, id.getType))
        val matchType = tupleTypeWrap(resId.getType +: freshIds.map(_.getType))

        val csesVals = csesRes.zip(csesFun).map {
          case (cRes, cFun) => tupleWrap(cRes +: modifiedVars.map(vId => cFun.getOrElse(vId, vId).toVariable))
        }

        val newRhs = csesVals.zip(csesScope).map {
          case (cVal, cScope) => replaceNames(scrutFun, cScope(cVal))
        }
        val matchE = matchExpr(scrutRes, cses.zip(newRhs).map {
          case (mc @ MatchCase(pat, guard, _), newRhs) =>
            //guard need to update ids (substitution of new names, and new fundef)
            //but wont have side effects
            val finalGuard = guard.map(g => {
              val (resGuard, scopeGuard, _) = toFunction(g)
              replaceNames(scrutFun, scopeGuard(resGuard))
            })
            MatchCase(pat, finalGuard, newRhs).setPos(mc)
        }).setPos(m)

        val scope = (body: Expr) => {
          val tupleId = FreshIdentifier("t", matchType)
          scrutScope(
            Let(tupleId, matchE,
              Let(resId, tupleSelect(tupleId.toVariable, 1, freshIds.nonEmpty),
                freshIds.zipWithIndex.foldLeft(body)((b, id) =>
                  Let(id._1, tupleSelect(tupleId.toVariable, id._2 + 2, true), b)
                )
              )
            )
          )
        }

        (resId.toVariable, scope, scrutFun ++ modifiedVars.zip(freshIds).toMap)
 
      case wh@While(cond, body) =>
        val whileFunDef = new FunDef(parent.id.duplicate(name = (parent.id.name + "While")), Nil, Nil, UnitType).setPos(wh)
        whileFunDef.addFlag(IsLoop(parent))
        whileFunDef.body = Some(
          IfExpr(cond, 
                 Block(Seq(body), FunctionInvocation(whileFunDef.typed, Seq()).setPos(wh)),
                 UnitLiteral()))
        whileFunDef.precondition = wh.invariant
        whileFunDef.postcondition = Some(
          Lambda(
            Seq(ValDef(FreshIdentifier("bodyRes", UnitType))),
            and(Not(getFunctionalResult(cond)), wh.invariant.getOrElse(BooleanLiteral(true))).setPos(wh)
          ).setPos(wh)
        )

        val newExpr = LetDef(Seq(whileFunDef), FunctionInvocation(whileFunDef.typed, Seq()).setPos(wh)).setPos(wh)
        toFunction(newExpr)

      case Block(Seq(), expr) =>
        toFunction(expr)

      case Block(exprs, expr) =>
        val (scope, fun) = exprs.foldRight((body: Expr) => body, Map[Identifier, Identifier]())((e, acc) => {
          val (accScope, accFun) = acc
          val (rVal, rScope, rFun) = toFunction(e)
          val scope = (body: Expr) => {
            rVal match {
              case FunctionInvocation(tfd, args) =>
                rScope(replaceNames(rFun, Let(FreshIdentifier("tmp", tfd.returnType), rVal, accScope(body))))
              case _ =>
                rScope(replaceNames(rFun, accScope(body)))
            }

          }
          (scope, rFun ++ accFun)
        })
        val (lastRes, lastScope, lastFun) = toFunction(expr)
        val finalFun = fun ++ lastFun
        (
          replaceNames(finalFun, lastRes),
          (body: Expr) => scope(replaceNames(fun, lastScope(body))),
          finalFun
        )

      //pure expression (that could still contain side effects as a subexpression) (evaluation order is from left to right)
      case Let(id, e, b) =>
        val (bindRes, bindScope, bindFun) = toFunction(e)
        val (bodyRes, bodyScope, bodyFun) = toFunction(b)
        (
          bodyRes, 
          (b2: Expr) => bindScope(Let(id, bindRes, replaceNames(bindFun, bodyScope(b2))).copiedFrom(expr)), 
          bindFun ++ bodyFun
        )

      //a function invocation can update variables in scope.
      case fi@FunctionInvocation(tfd, args) =>


        val (recArgs, argScope, argFun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })

        val fd = tfd.fd
        state.funDefsMapping.get(fd) match { 
          case Some((newFd, modifiedVars)) => {
            val newInvoc = FunctionInvocation(newFd.typed, recArgs ++ modifiedVars.map(id => id.toVariable)).setPos(fi)
            val freshNames = modifiedVars.map(id => id.freshen)
            val tmpTuple = FreshIdentifier("t", newFd.returnType)

            val scope = (body: Expr) => {
              argScope(Let(tmpTuple, newInvoc,
                freshNames.zipWithIndex.foldRight(body)((p, b) =>
                  Let(p._1, TupleSelect(tmpTuple.toVariable, p._2 + 2), b))
              ))
            }
            val newMap = argFun ++ modifiedVars.zip(freshNames).toMap

            (TupleSelect(tmpTuple.toVariable, 1), scope, newMap)
          }
          case None =>
            (FunctionInvocation(tfd, recArgs).copiedFrom(fi), argScope, argFun)
        }


      case LetDef(fds, b) =>

        if(fds.size > 1) {
          //TODO: no support for true mutual recursion
          toFunction(LetDef(Seq(fds.head), LetDef(fds.tail, b)))
        } else {

          val fd = fds.head

          def fdWithoutSideEffects =  {
            fd.body.foreach { bd =>
              val (fdRes, fdScope, _) = toFunction(bd)
              fd.body = Some(fdScope(fdRes))
            }
            val (bodyRes, bodyScope, bodyFun) = toFunction(b)
            (bodyRes, (b2: Expr) => LetDef(Seq(fd), bodyScope(b2)).setPos(fd).copiedFrom(expr), bodyFun)
          }

          fd.body match {
            case Some(bd) => {

              //we take any vars in scope needed (even for read only).
              //if read only, we only need to capture it without returning, but
              //returning it simplifies the code (more consistent) and should
              //not have a big impact on performance
              val modifiedVars: List[Identifier] = {
                val freeVars = variablesOf(fd.fullBody)
                val transitiveVars = collect[Identifier]({
                  case FunctionInvocation(tfd, _) => state.funDefsMapping.get(tfd.fd).map(p => p._2.toSet).getOrElse(Set())
                  case _ => Set()
                })(fd.fullBody)
                (freeVars ++ transitiveVars).intersect(state.varsInScope).toList
              }
              //val modifiedVars: List[Identifier] =
              //  collect[Identifier]({
              //    case Assignment(v, _) => Set(v)
              //    case FunctionInvocation(tfd, _) => state.funDefsMapping.get(tfd.fd).map(p => p._2.toSet).getOrElse(Set())
              //    case _ => Set()
              //  })(bd).intersect(state.varsInScope).toList

              if(modifiedVars.isEmpty) fdWithoutSideEffects else {

                val freshNames: List[Identifier] = modifiedVars.map(id => id.freshen)

                val newParams: Seq[ValDef] = fd.params ++ freshNames.map(n => ValDef(n))
                val freshVarDecls: List[Identifier] = freshNames.map(id => id.freshen)

                val rewritingMap: Map[Identifier, Identifier] =
                  modifiedVars.zip(freshVarDecls).toMap
                val freshBody =
                  preMap({
                    case Assignment(v, e) => rewritingMap.get(v).map(nv => Assignment(nv, e))
                    case Variable(id) => rewritingMap.get(id).map(nid => Variable(nid))
                    case _ => None
                  })(bd)
                val wrappedBody = freshNames.zip(freshVarDecls).foldLeft(freshBody)((body, p) => {
                  LetVar(p._2, Variable(p._1), body)
                })

                val newReturnType = TupleType(fd.returnType :: modifiedVars.map(_.getType))

                val newFd = new FunDef(fd.id.freshen, fd.tparams, newParams, newReturnType).setPos(fd)
                newFd.addFlags(fd.flags)

                val (fdRes, fdScope, fdFun) = 
                  toFunction(wrappedBody)(
                    State(state.parent, 
                          Set(), 
                          state.funDefsMapping.map{case (fd, (nfd, mvs)) => (fd, (nfd, mvs.map(v => rewritingMap.getOrElse(v, v))))} + 
                                 (fd -> ((newFd, freshVarDecls))))
                  )
                val newRes = Tuple(fdRes :: freshVarDecls.map(vd => fdFun(vd).toVariable))
                val newBody = fdScope(newRes)

                newFd.body = Some(newBody)
                newFd.precondition = fd.precondition.map(prec => {
                  val fresh = replace(modifiedVars.zip(freshNames).map(p => (p._1.toVariable, p._2.toVariable)).toMap, prec)
                  //still apply recursively to update all function invocation
                  val (res, scope, _) = toFunction(fresh)
                  scope(res)
                })
                newFd.postcondition = fd.postcondition.map(post => {
                  val Lambda(Seq(res), postBody) = post
                  val newRes = ValDef(FreshIdentifier(res.id.name, newFd.returnType))

                  val newBody =
                    replace(
                      modifiedVars.zipWithIndex.map{ case (v, i) => 
                        (v.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap ++
                      modifiedVars.zip(freshNames).map{ case (ov, nv) => 
                        (Old(ov), nv.toVariable)}.toMap +
                      (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
                    postBody)

                  val (r, scope, _) = toFunction(newBody)

                  Lambda(Seq(newRes), scope(r)).setPos(post)
                })

                val (bodyRes, bodyScope, bodyFun) = toFunction(b)(state.withFunDef(fd, newFd, modifiedVars))
                (bodyRes, (b2: Expr) => LetDef(Seq(newFd), bodyScope(b2)).copiedFrom(expr), bodyFun)
              }
            }
            case None => fdWithoutSideEffects
          }
        }

      //TODO: handle vars in scope, just like LetDef
      case ld@Lambda(params, body) =>
        val (bodyVal, bodyScope, bodyFun) = toFunction(body)
        (Lambda(params, bodyScope(bodyVal)).copiedFrom(ld), (e: Expr) => e, Map())

      case c @ Choose(b) =>
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
      case a@Assert(cond, msg, body) =>
        val (condVal, condScope, condFun) = toFunction(cond)
        val (bodyRes, bodyScope, bodyFun) = toFunction(body)
        val scope = (body: Expr) => condScope(Assert(condVal, msg, replaceNames(condFun, bodyScope(body))).copiedFrom(a))
        (bodyRes, scope, condFun ++ bodyFun)


      case n @ Operator(args, recons) =>
        val (recArgs, scope, fun) = args.foldRight((Seq[Expr](), (body: Expr) => body, Map[Identifier, Identifier]()))((arg, acc) => {
          val (accArgs, accScope, accFun) = acc
          val (argVal, argScope, argFun) = toFunction(arg)
          val newScope = (body: Expr) => argScope(replaceNames(argFun, accScope(body)))
          (argVal +: accArgs, newScope, argFun ++ accFun)
        })

        (recons(recArgs).copiedFrom(n), scope, fun)

      case _ =>
        sys.error("not supported: " + expr)
    }
  }

  def replaceNames(fun: Map[Identifier, Identifier], expr: Expr) = replaceFromIDs(fun mapValues Variable, expr)

  
  /* Extract functional result value. Useful to remove side effect from conditions when moving it to post-condition */
  private def getFunctionalResult(expr: Expr): Expr = {
    preMap({
      case Block(_, res) => Some(res)
      case _ => None
    })(expr)
  }

  private def requireRewriting(expr: Expr) = expr match {
    case (e: Block) => true
    case (e: Assignment) => true
    case (e: While) => true
    case (e: LetVar) => true
    case _ => false
  }

}
