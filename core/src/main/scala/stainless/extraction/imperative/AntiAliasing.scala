/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox._

trait AntiAliasing
  extends CachingPhase
     with SimpleSorts
     with EffectsAnalyzer
     with EffectsChecker
     with GhostChecker { self =>
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new DependencyCache[s.FunDef, FunctionResult]

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new DependencyCache[s.ADTSort, SortResult]

  override protected type FunctionResult = Option[FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected case class SymbolsAnalysis(symbols: Symbols, effects: EffectsAnalysis) {
    import symbols._

    // Convert a function type with mutable parameters, into a function type
    // that returns the mutable parameters. This makes explicit all possible
    // effects of the function. This should be used for higher order functions
    // declared as parameters.
    def makeFunctionTypeExplicit(tpe: FunctionType): FunctionType = {
      val newReturnTypes = tpe.from.filter(t => isMutableType(t))
      if (newReturnTypes.isEmpty) tpe
      else FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
    }

    object transformer extends SelfTreeTransformer {

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
  }

  override protected type TransformerContext = SymbolsAnalysis
  override protected def getContext(symbols: Symbols) = SymbolsAnalysis(symbols, EffectsAnalysis(symbols))

  override protected def extractFunction(analysis: SymbolsAnalysis, fd: FunDef): Option[FunDef] = {
    import analysis._
    import symbols._

    checkGhost(fd)(symbols, effects)

    checkEffects(fd)(symbols, effects) match {
      case CheckResult.Ok => ()
      case CheckResult.Skip => return None
      case CheckResult.Error(err) => throw err
    }

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

      val newFd = fd.copy(returnType = effects.getReturnType(fd))

      if (aliasedParams.isEmpty) {
        newFd.copy(fullBody = makeSideEffectsExplicit(fd.fullBody, fd, env))
      } else {
        val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)
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

        val newSpecs = specs.map {
          case exprOps.Postcondition(post @ Lambda(Seq(res), postBody)) =>
            val newRes = ValDef(res.id.freshen, newFd.returnType).copiedFrom(res)
            val newBody = exprOps.replaceSingle(
              aliasedParams.map(vd => (Old(vd.toVariable), vd.toVariable): (Expr, Expr)).toMap ++
              aliasedParams.zipWithIndex.map { case (vd, i) =>
                (vd.toVariable, TupleSelect(newRes.toVariable, i+2).copiedFrom(vd)): (Expr, Expr)
              }.toMap + (res.toVariable -> TupleSelect(newRes.toVariable, 1).copiedFrom(res)),
              makeSideEffectsExplicit(postBody, fd, env)
            )

            exprOps.Postcondition(Lambda(Seq(newRes), newBody).copiedFrom(post))

          case spec => spec
        }

        newFd.copy(fullBody = exprOps.reconstructSpecs(newSpecs, newBody, newFd.returnType))
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
        val trees: self.s.type = self.s
        type Env = Environment
        val initEnv: Env = env

        def mapApplication(formalArgs: Seq[ValDef], args: Seq[Expr], nfi: Expr, nfiType: Type, fiEffects: Set[Effect], env: Env): Expr = {
          if (fiEffects.exists(e => formalArgs contains e.receiver.toVal)) {
            val localEffects = (formalArgs zip args)
              .map { case (vd, arg) => (fiEffects.filter(_.receiver == vd.toVariable), arg) }
              .filter { case (effects, _) => effects.nonEmpty }
              .map { case (effects, arg) =>
                val rArg = exprOps.replaceFromSymbols(env.rewritings, arg)
                effects map (e => (e, e on rArg))
              }

            for ((_, effects) <- localEffects.flatMap(_.flatMap(_._2)).groupBy(_.receiver)) {
              val aliased = effects.toSeq.tails.flatMap {
                case e1 +: es => es.collect { case e2 if (e1 prefixOf e2) || (e2 prefixOf e1) => (e1, e2) }
                case Nil => Nil
              }

              if (aliased.nonEmpty) {
                val (e1, _) = aliased.next
                throw MissformedStainlessCode(e1.receiver, "Illegal passing of aliased parameter")
              }
            }

            //TODO: The case f(A(x1,x1,x1)) could probably be handled by forbidding creation at any program point of
            //      case class with multiple refs as it is probably not useful

            val freshRes = ValDef(FreshIdentifier("res"), nfiType).copiedFrom(nfi)

            val extractResults = Block(
              for {
                (effects, index) <- localEffects.zipWithIndex
                (outerEffect, innerEffects) <- effects
                effect <- innerEffects
              } yield {
                val pos = args(index).getPos
                val resSelect = TupleSelect(freshRes.toVariable, index + 2)

                def select(tpe: Type, expr: Expr, path: Seq[Accessor]): (Expr, Expr) = (tpe, path) match {
                  case (adt: ADTType, FieldAccessor(id) +: xs) =>
                    val constructors = adt.getSort.constructors
                    val constructor = constructors.find(_.fields.exists(_.id == id)).get
                    val field = constructor.fields.find(_.id == id).get

                    val condition = if (constructors.size > 1) {
                      IsConstructor(expr, constructor.id).setPos(pos)
                    } else {
                      BooleanLiteral(true).setPos(pos)
                    }

                    val (recCond, recSelect) = select(field.tpe, ADTSelector(expr, id).setPos(pos), xs)
                    (and(condition, recCond), recSelect)

                  case (ArrayType(base), ArrayAccessor(idx) +: xs) =>
                    select(base, ArraySelect(expr, idx).setPos(pos), xs)

                  case (_, Nil) => (BooleanLiteral(true).setPos(pos), expr)
                }

                val (cond, result) = select(resSelect.getType, resSelect, outerEffect.target.path)
                val newValue = applyEffect(effect, Annotated(result, Seq(Unchecked)).setPos(pos))
                val assignment = Assignment(effect.receiver, newValue).setPos(args(index))

                if (cond == BooleanLiteral(true)) assignment
                else IfExpr(cond, assignment, UnitLiteral().setPos(pos)).setPos(pos)
              },
              TupleSelect(freshRes.toVariable, 1))

            if (isMutableType(nfiType)) {
              LetVar(freshRes, nfi, rec(extractResults, env withBinding freshRes))
            } else {
              Let(freshRes, nfi, rec(extractResults, env))
            }
          } else {
            nfi
          }
        }

        protected def rec(e: Expr, env: Env): Expr = (e match {
          case l @ Let(vd, e, b) if isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            getKnownEffect(newExpr) match {
              case Some(_) =>
                val newBody = rec(b, env withRewritings Map(vd -> newExpr))
                Let(vd, newExpr, newBody).copiedFrom(l)

              case None =>
                val newBody = rec(b, env withBinding vd)
                LetVar(vd, newExpr, newBody).copiedFrom(l)
            }

          case l @ LetVar(vd, e, b) if isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            val newBody = rec(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case m @ MatchExpr(scrut, cses) if isMutableType(scrut.getType) =>
            if (effects(scrut).nonEmpty) {
              def liftEffects(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
                case ArraySelect(e, i) if effects(i).nonEmpty =>
                  val (eBindings, eLift) = liftEffects(e)
                  val vd = ValDef(FreshIdentifier("index", true), Int32Type().copiedFrom(i)).copiedFrom(i)
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
            val effect = getExactEffect(ra)
            if (env.bindings contains effect.receiver.toVal) {
              val applied = applyEffect(effect + ArrayAccessor(i), v)
              rec(Assignment(effect.receiver, applied).copiedFrom(up), env)
            } else {
              throw MissformedStainlessCode(up, "Unsupported form of array update")
            }

          case as @ FieldAssignment(o, id, v) =>
            val so = exprOps.replaceFromSymbols(env.rewritings, o)
            val effect = getExactEffect(so)
            if (env.bindings contains effect.receiver.toVal) {
              val applied = applyEffect(effect + FieldAccessor(id), v)
              rec(Assignment(effect.receiver, applied).copiedFrom(as), env)
            } else {
              throw MissformedStainlessCode(as, "Unsupported form of field assignment")
            }

          //we need to replace local fundef by the new updated fun defs.
          case l @ LetRec(fds, body) =>
            val nfds = fds.map(fd => updateFunction(Inner(fd), env withLocals fds).toLocal)
            LetRec(nfds, rec(body, env withLocals fds)).copiedFrom(l)

          case e @ Ensuring(body, l @ Lambda(params, post)) =>
            Ensuring(rec(body, env), Lambda(params, rec(post, env)).copiedFrom(l)).copiedFrom(e)

          case l @ Lambda(params, body) =>
            val ft @ FunctionType(_, _) = l.getType
            val ownEffects = functionTypeEffects(ft)
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
            mapApplication(fd.params, args, nfi, fi.tfd.instantiate(effects.getReturnType(fd)), effects(fd), env)

          case alr @ ApplyLetRec(fun, tparams, tps, args) =>
            val fd = Inner(env.locals(fun.toVal))
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = ApplyLetRec(
              fun.copy(tpe = FunctionType(fd.params.map(_.tpe), effects.getReturnType(fd))), tparams, tps,
              args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(alr)
            val resultType = typeOps.instantiateType(effects.getReturnType(fd), (tparams zip tps).toMap)
            mapApplication(fd.params, args, nfi, resultType, effects(fd), env)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType
            val ftEffects = functionTypeEffects(ft)
            if (ftEffects.nonEmpty) {
              val nfi = Application(rec(callee, env), args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(app)
              val params = from.map(tpe => ValDef.fresh("x", tpe))
              val appEffects = params.zipWithIndex.collect { case (vd, i) if ftEffects(i) => Effect(vd.toVariable, Target(Seq())) }
              mapApplication(params, args, nfi, makeFunctionTypeExplicit(ft).to, appEffects.toSet, env)
            } else {
              Application(rec(callee, env), args.map(rec(_, env))).copiedFrom(app)
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
      freeVars.filter(v => isMutableType(v.tpe))
    }

    //given a receiver object (mutable class or array, usually as a reference id),
    //and a path of field/index access, build a copy of the original object, with
    //properly updated values
    def applyEffect(effect: Effect, newValue: Expr): Expr = {
      def rec(receiver: Expr, path: Seq[Accessor]): Expr = path match {
        case FieldAccessor(id) :: fs =>
          val adt @ ADTType(_, tps) = receiver.getType
          val tcons = adt.getSort.constructors.find(_.fields.exists(_.id == id)).get
          val r = rec(Annotated(ADTSelector(receiver, id).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)

          ADT(tcons.id, tps, tcons.definition.fields.map { vd =>
            if (vd.id == id) r
            else Annotated(ADTSelector(receiver, vd.id).copiedFrom(receiver), Seq(Unchecked)).copiedFrom(receiver)
          }).copiedFrom(newValue)

        case ArrayAccessor(index) :: fs =>
          val r = rec(Annotated(ArraySelect(receiver, index).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)
          ArrayUpdated(receiver, index, r).copiedFrom(newValue)

        case Nil => newValue
      }

      rec(effect.receiver, effect.target.path)
    }

    Some(transformer.transform(updateFunction(Outer(fd), Environment.empty).toFun))
  }

  override protected def extractSort(analysis: SymbolsAnalysis, sort: ADTSort): ADTSort =
    analysis.transformer.transform(sort)
}

object AntiAliasing {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new AntiAliasing {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
