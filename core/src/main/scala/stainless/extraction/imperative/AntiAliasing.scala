/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox._

trait AntiAliasing extends inox.ast.SymbolTransformer with EffectsChecking { self =>
  val trees: Trees
  lazy val s: trees.type = trees
  lazy val t: trees.type = trees
  import trees._

  def transform(syms: Symbols): Symbols = {

    object transformer extends SelfTreeTransformer {
      import syms._

      object effects extends {
        val trees: self.trees.type = self.trees
        val symbols: syms.type = syms
      } with EffectsAnalysis

      //convert a function type with mutable parameters, into a function type
      //that returns the mutable parameters. This makes explicit all possible
      //effects of the function. This should be used for higher order functions
      //declared as parameters.
      def makeFunctionTypeExplicit(tpe: FunctionType): FunctionType = {
        val newReturnTypes = tpe.from.filter(t => effects.isMutableType(t))
        if (newReturnTypes.isEmpty) tpe
        else FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
      }

      // XXX: since LetRec and ApplyLetRec use the fun variable to encode
      //      the type of the corresponding function, we have to make sure to
      //      NOT make that first-class function type explicit!!
      override def transform(e: Expr): Expr = e match {
        case LetRec(fds, body) =>
          LetRec(fds.map { case LocalFunDef(fun, tparams, body) =>
            val FunctionType(from, to) = fun.tpe
            LocalFunDef(
              fun.copy(tpe = FunctionType(from map transform, transform(to))),
              tparams map transform,
              transform(body).asInstanceOf[Lambda]
            )
          }, transform(body)).copiedFrom(e)

        case ApplyLetRec(fun, tparams, tps, args) =>
          val FunctionType(from, to) = fun.tpe
          ApplyLetRec(
            fun.copy(tpe = FunctionType(from map transform, transform(to))),
            tparams map (tp => transform(tp).asInstanceOf[TypeParameter]),
            tps map transform,
            args map transform
          ).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ft: FunctionType => makeFunctionTypeExplicit(ft)
        case _ => super.transform(tpe)
      }
    }

    val newSyms = syms.transform(transformer)
    import newSyms._

    object effects extends {
      val trees: self.trees.type = self.trees
      val symbols: newSyms.type = newSyms
    } with EffectsAnalysis

    checkEffects(effects)

    type Environment = (Set[ValDef], Map[ValDef, Expr], Map[ValDef, LocalFunDef])
    implicit class EnvWrapper(env: Environment) {
      val (bindings, rewritings, locals) = env
      def withBinding(vd: ValDef): Environment = (bindings + vd, rewritings, locals)
      def withBindings(vds: Iterable[ValDef]): Environment = (bindings ++ vds, rewritings, locals)
      def withRewritings(map: Map[ValDef, Expr]): Environment = (bindings, rewritings ++ map, locals)
      def withLocals(fds: Seq[LocalFunDef]): Environment = (bindings, rewritings, locals ++ fds.map(fd => fd.name -> fd))
    }

    object Environment {
      def empty: Environment = (Set.empty, Map.empty, Map.empty)
    }

    /* Create a new FunDef for a given FunDef in the program.
     * Adapt the signature to express its effects. In case the
     * function has no effect, this will still return the original
     * fundef.
     *
     * Also update FunctionType parameters that need to become explicit
     * about the effect they could perform (returning any mutable type that
     * they receive).
     */
    def updateFunction(fd: FunAbstraction, env: Environment): FunAbstraction = {
      val aliasedParams = effects.getAliasedParams(fd)

      //val newParams = fd.params.map(vd => vd.getType match {
      //  case (ft: FunctionType) => {
      //    val nft = makeFunctionTypeExplicit(ft)
      //    if(ft == nft) vd else ValDef(vd.id.duplicate(tpe = nft))
      //  }
      //  case (cct: CaseClassType) => ccdMap.get(cct.classDef) match {
      //    case Some(ncd) => ValDef(vd.id.duplicate(tpe = ncd.typed))
      //    case None => vd
      //  }
      //  case _ => vd
      //})

      effects.getReturnedExpressions(fd.fullBody).foreach {
        case v: Variable if aliasedParams.contains(v.toVal) =>
          throw FatalError("Cannot return a shared reference to a mutable object")
        case _ => ()
      }

      val newFd = fd.copy(returnType = effects.getReturnType(fd))

      if (aliasedParams.isEmpty) {
        val (pre, body, post) = exprOps.breakDownSpecs(fd.fullBody)
        val newBody = body.map(makeSideEffectsExplicit(_, fd, env))
        val newFullBody = exprOps.reconstructSpecs(pre, newBody, post, newFd.returnType)
        if (!newFullBody.getPos.isDefined) newFullBody.setPos(newFd)
        newFd.copy(fullBody = newFullBody)
      } else {
        val (pre, body, post) = exprOps.breakDownSpecs(fd.fullBody)
        val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
        val freshSubst = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap

        val newBody = body.map { body =>
          val freshBody = exprOps.replaceFromSymbols(freshSubst, body)
          val explicitBody = makeSideEffectsExplicit(freshBody, fd, env withBindings freshLocals)

          //WARNING: only works if side effects in Tuples are extracted from left to right,
          //         in the ImperativeTransformation phase.
          val finalBody: Expr = Tuple(explicitBody +: freshLocals.map(_.toVariable)).copiedFrom(body)

          freshLocals.zip(aliasedParams).foldLeft(finalBody) {
            (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(body)
          }
        }

        val newPost = post.map { post =>
          val Lambda(Seq(res), postBody) = post
          val newRes = ValDef(res.id.freshen, newFd.returnType, Set.empty).copiedFrom(res)
          val newBody = exprOps.replaceSingle(
            aliasedParams.map(vd => (Old(vd.toVariable), vd.toVariable): (Expr, Expr)).toMap ++
            aliasedParams.zipWithIndex.map { case (vd, i) =>
              (vd.toVariable, TupleSelect(newRes.toVariable, i+2).copiedFrom(vd)): (Expr, Expr)
            }.toMap + (res.toVariable -> TupleSelect(newRes.toVariable, 1).copiedFrom(res)),
            postBody
          )

          Lambda(Seq(newRes), newBody).copiedFrom(post)
        }

        newFd.copy(fullBody = exprOps.reconstructSpecs(pre, newBody, newPost, newFd.returnType))
      }
    }

    //We turn all local val of mutable objects into vars and explicit side effects
    //using assignments. We also make sure that no aliasing is being done.
    def makeSideEffectsExplicit(
      body: Expr,
      originalFd: FunAbstraction,
      env: Environment
    ): Expr = {

      object transformer extends inox.transformers.Transformer {
        val trees: self.trees.type = self.trees
        type Env = Environment
        val initEnv: Env = env

        def mapApplication(args: Seq[Expr], nfi: Expr, nfiType: Type, fiEffects: Set[Int], env: Env): Expr = {
          if (fiEffects.nonEmpty) {
            val modifiedArgs: Seq[(Seq[Variable], Expr)] = args.zipWithIndex
              .filter { case (arg, i) => fiEffects.contains(i) }
              .map { arg =>
                val rArg = exprOps.replaceFromSymbols(env.rewritings, arg._1)
                (effects.getReferencedVariables(rArg).filter(v => effects.isMutableType(v.tpe)), rArg)
              }

            val allParams: Seq[Variable] = modifiedArgs.flatMap(_._1)
            val duplicatedParams = allParams.diff(allParams.distinct).distinct
            if (duplicatedParams.nonEmpty)
              throw FatalError("Illegal passing of aliased parameter: " + duplicatedParams.head)

            //TODO: The case f(A(x1,x1,x1)) could probably be handled by forbidding creation at any program point of
            //      case class with multiple refs as it is probably not useful

            val freshRes = ValDef(FreshIdentifier("res"), nfiType, Set.empty)

            val extractResults = Block(
              for (((varsForIndex, expr), index) <- modifiedArgs.zipWithIndex; v <- varsForIndex) yield {
                val resSelect = TupleSelect(freshRes.toVariable, index + 2)
                val newValue = expr match {
                  case cs: ADTSelector =>
                    val (rec, path) = fieldPath(cs)
                    objectUpdateToCopy(rec, path, resSelect)

                  case as: ArraySelect =>
                    val (rec, path) = fieldPath(as)
                    objectUpdateToCopy(rec, path, resSelect)

                  case cc @ ADT(adt, es) =>
                    val (_, vd) = (es zip adt.getADT.toConstructor.definition.fields).find {
                      case (va: Variable, _) => va == v
                      case _ => false
                    }.get
                    ADTSelector(resSelect, vd.id)
                    //TODO: this only checks for a top level modified id,
                    //      must generalize to any number of nested case classes
                    //      must also handle combination of case class and selectors

                  case _ => resSelect
                }

                Assignment(v, v.tpe match {
                  case adt: ADTType if adt != newValue.getType => AsInstanceOf(newValue, adt).setPos(expr.getPos)
                  case _ => newValue
                }).setPos(expr.getPos)
              },
              TupleSelect(freshRes.toVariable, 1))

            if (effects.isMutableType(nfiType)) {
              LetVar(freshRes, nfi, rec(extractResults, env withBinding freshRes))
            } else {
              Let(freshRes, nfi, rec(extractResults, env))
            }
          } else {
            nfi
          }
        }

        protected def rec(e: Expr, env: Env): Expr = (e match {
          case l @ Let(vd, e, b) if effects.isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            val newBody = rec(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case l @ LetVar(vd, e, b) if effects.isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            val newBody = rec(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case m @ MatchExpr(scrut, cses) if effects.isMutableType(scrut.getType) =>
            if (effects(scrut).nonEmpty) {
              def liftEffects(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
                case ArraySelect(e, i) if effects(i).nonEmpty =>
                  val (eBindings, eLift) = liftEffects(e)
                  val vd = ValDef(FreshIdentifier("index", true), Int32Type).copiedFrom(i)
                  (eBindings :+ (vd -> i), ArraySelect(eLift, vd.toVariable).copiedFrom(e))
                case _ if effects(e).nonEmpty =>
                  throw MissformedStainlessCode(m, "Unexpected effects in match scrutinee")
                case _ => (Seq.empty, e)
              }

              val (bindings, newScrut) = liftEffects(scrut)
              val newMatch = bindings.foldRight(MatchExpr(newScrut, cses).copiedFrom(m): Expr) {
                case ((vd, e), b) => Let(vd, e, b).copiedFrom(m)
              }
              rec(newMatch, env)
            } else {
              val newScrut = rec(scrut, env)
              val newCases = cses.map { case mc @ MatchCase(pattern, guard, rhs) =>
                val newRewritings = mapForPattern(newScrut, pattern)
                val newGuard = guard.map(rec(_, env withRewritings newRewritings))
                val newRhs = rec(rhs, env withRewritings newRewritings)
                MatchCase(pattern, newGuard, newRhs).copiedFrom(mc)
              }
              MatchExpr(newScrut, newCases).copiedFrom(m)
            }

          case up @ ArrayUpdate(a, i, v) =>
            val ra = exprOps.replaceFromSymbols(env.rewritings, a)
            val (receiver, path) = fieldPath(ra, List(ArrayIndex(i)))

            effects.getReceiverVariable(receiver) match {
              case None => throw FatalError("Unsupported form of array update: " + up)
              case Some(ov) =>
                if (env.bindings.contains(ov.toVal)) {
                  rec(Assignment(ov, objectUpdateToCopy(receiver, path, v).copiedFrom(up)).copiedFrom(up), env)
                } else {
                  throw FatalError("Unsupported form of array update: " + up)
                }
            }

          case as @ FieldAssignment(o, id, v) =>
            val so = exprOps.replaceFromSymbols(env.rewritings, o)
            val (receiver, path) = fieldPath(so, List(ADTField(id)))

            effects.getReceiverVariable(so) match {
              case None => throw FatalError("Unsupported form of field assignment: " + as)
              case Some(ov) =>
                if (env.bindings.contains(ov.toVal)) {
                  rec(Assignment(ov, objectUpdateToCopy(receiver, path, v).copiedFrom(as)).copiedFrom(as), env)
                } else {
                  throw FatalError("Unsupported form of field assignment: " + as)
                }
            }

          //we need to replace local fundef by the new updated fun defs.
          case l @ LetRec(fds, body) =>
            val nfds = fds.map(fd => updateFunction(Inner(fd), env withLocals fds).toLocal)
            LetRec(nfds, rec(body, env withLocals fds)).copiedFrom(l)

          case e @ Ensuring(body, l @ Lambda(params, post)) =>
            Ensuring(rec(body, env), Lambda(params, rec(post, env)).copiedFrom(l)).copiedFrom(e)

          case l @ Lambda(params, body) =>
            val ft @ FunctionType(_, _) = l.getType
            val ownEffects = effects.functionTypeEffects(ft)
            val aliasedParams: Seq[ValDef] = params.zipWithIndex.flatMap {
              case (vd, i) if ownEffects.contains(i) => Some(vd)
              case _ => None
            }

            if (aliasedParams.isEmpty) {
              Lambda(params, rec(body, env)).copiedFrom(l)
            } else {
              val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
              val rewritingMap: Map[Variable, Variable] = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap
              val freshBody = exprOps.replaceFromSymbols(rewritingMap, body)

              //WARNING: only works if side effects in Tuples are extracted from left to right,
              //         in the ImperativeTransformation phase.
              val finalBody: Expr = Tuple(freshBody +: freshLocals.map(_.toVariable))

              val wrappedBody: Expr = freshLocals.zip(aliasedParams).foldLeft(finalBody) {
                (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(bd)
              }
              Lambda(params, rec(wrappedBody, env)).copiedFrom(l)
            }

          case fi @ FunctionInvocation(id, tps, args) =>
            val fd = Outer(fi.tfd.fd)
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = FunctionInvocation(id, tps, args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(fi)
            mapApplication(args, nfi, fi.tfd.instantiate(effects.getReturnType(fd)), effects(fd), env)

          case alr @ ApplyLetRec(fun, tparams, tps, args) =>
            val fd = Inner(env.locals(fun.toVal))
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = ApplyLetRec(
              fun.copy(tpe = FunctionType(fd.params.map(_.tpe), effects.getReturnType(fd))), tparams, tps,
              args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(alr)
            val resultType = instantiateType(effects.getReturnType(fd), (tparams zip tps).toMap)
            mapApplication(args, nfi, resultType, effects(fd), env)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(_, to) = callee.getType
            to match {
              case TupleType(tps) if effects.isMutableType(tps.last) =>
                val nfi = Application(rec(callee, env), args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(app)
                mapApplication(args, nfi, to, effects.functionTypeEffects(ft), env)
              case _ => Application(rec(callee, env), args.map(rec(_, env)))
            }

          case Operator(es, recons) => recons(es.map(rec(_, env)))
        }).copiedFrom(e)
      }

      transformer.transform(body)
    }


    //for each fun def, all the vars the the body captures.
    //Only mutable types.
    def varsInScope(fd: FunAbstraction): Set[Variable] = {
      val allFreeVars = exprOps.variablesOf(fd.fullBody)
      val freeVars = allFreeVars -- fd.params.map(_.toVariable)
      freeVars.filter(v => effects.isMutableType(v.tpe))
    }


    //private def extractFieldPath(o: Expr): (Expr, List[Identifier]) = {
    //  def rec(o: Expr): List[Identifier] = o match {
    //    case CaseClassSelector(_, r, i) =>
    //      val res = toFieldPath(r)
    //      (res._1, i::res)
    //    case expr => (expr, Nil)
    //  }
    //  val res = rec(o)
    //  (res._1, res._2.reverse)
    //}

    sealed trait Field
    case class ADTField(id: Identifier) extends Field
    case class ArrayIndex(e: Expr) extends Field

    //given a nested arrayselect and class selectors, return the receiver expression along
    //with the path from left to right
    //Does not consider FieldAssignment and ArrayUpdate as they only make sense on
    //the first level, and it seems cleaner to define path only on select operators
    def fieldPath(e: Expr, accPath: List[Field] = Nil): (Expr, List[Field]) = e match {
      case ADTSelector(r, id) => fieldPath(r, ADTField(id) :: accPath)
      case ArraySelect(a, index) => fieldPath(a, ArrayIndex(index) :: accPath)
      case e => (e, accPath)
    }

    //given a receiver object (mutable class or array, usually as a reference id),
    //and a path of field/index access, build a copy of the original object, with
    //properly updated values
    def objectUpdateToCopy(receiver: Expr, path: List[Field], newValue: Expr): Expr = path match {
      case ADTField(id) :: fs =>
        val adt @ ADTType(_, _) = receiver.getType
        val rec = objectUpdateToCopy(ADTSelector(receiver, id), fs, newValue).setPos(newValue)

        ADT(adt, adt.getADT.toConstructor.definition.fields.map { vd =>
          if (vd.id == id) rec
          else ADTSelector(receiver, vd.id).copiedFrom(receiver)
        })

      case ArrayIndex(index) :: fs =>
        val rec = objectUpdateToCopy(ArraySelect(receiver, index).setPos(newValue), fs, newValue)
        ArrayUpdated(receiver, index, rec).setPos(newValue)

      case Nil => newValue
    }

    val finalSyms = NoSymbols
      .withADTs(newSyms.adts.values.toSeq)
      .withFunctions(for (fd <- newSyms.functions.values.toSeq) yield {
        updateFunction(Outer(fd), Environment.empty).toFun
      })

    finalSyms
  }
}
