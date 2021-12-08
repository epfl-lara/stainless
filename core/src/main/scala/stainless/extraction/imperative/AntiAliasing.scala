/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

import scala.util.Try

class AntiAliasing(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with EffectsAnalyzer
     with EffectsChecker
     with GhostChecker { self =>
  import s._
  import exprOps._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult]((sort, context) =>
    getDependencyKey(sort.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult]((cd, context) =>
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
    def makeFunctionTypeExplicit(tpe: Type): Type = tpe match {
      case ft @ FunctionType(from, to) =>
        ft.copy(to = tupleTypeWrap(to +: from.filter(isMutableType(_))).copiedFrom(to)).copiedFrom(tpe)
      case pt @ PiType(params, to) =>
        pt.copy(to = tupleTypeWrap(to +: params.map(_.tpe).filter(isMutableType(_))).copiedFrom(to)).copiedFrom(tpe)
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

  override protected def extractFunction(analysis: SymbolsAnalysis, fd: FunDef): Option[FunDef] = {
    import analysis.{given, _}
    import symbols._

    checkGhost(fd)(analysis)

    checkEffects(fd)(analysis) match {
      case CheckResult.Ok => ()
      case CheckResult.Skip => return None
      case CheckResult.Error(err) => throw err
    }

    type Environment = (Set[ValDef], Map[ValDef, Expr], Map[Identifier, LocalFunDef])
    extension (env: Environment) {
      def bindings: Set[ValDef] = env._1
      def rewritings: Map[ValDef, Expr] = env._2
      def locals: Map[Identifier, LocalFunDef] = env._3
      def withBinding(vd: ValDef): Environment = (bindings + vd, rewritings, locals)
      def withBindings(vds: Iterable[ValDef]): Environment = (bindings ++ vds, rewritings, locals)
      def withRewritings(map: Map[ValDef, Expr]): Environment = (bindings, rewritings ++ map, locals)
      def withLocals(fds: Seq[LocalFunDef]): Environment = (bindings, rewritings, locals ++ fds.map(fd => fd.id -> fd))
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
      val aliasedParams = analysis.getAliasedParams(fd)
      val newFd = fd.copy(returnType = analysis.getReturnType(fd))

      if (aliasedParams.isEmpty) {
        newFd.copy(fullBody = makeSideEffectsExplicit(fd.fullBody, fd, env, Seq.empty))
      } else {
        val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)
        val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
        val freshSubst = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap

        val newBody = body.map { body =>
          val freshBody = exprOps.replaceFromSymbols(freshSubst, body)
          val explicitBody = makeSideEffectsExplicit(freshBody, fd, env withBindings freshLocals, freshLocals.map(_.toVariable))

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
              makeSideEffectsExplicit(postBody, fd, env, Seq.empty)
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
      env: Environment,
      freshLocals: Seq[Variable]
    ): Expr = {
      class TransformerImpl(override val s: self.s.type, override val t: self.t.type)
        extends inox.transformers.Transformer {
        override type Env = Environment

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
        }

        def makeAssignment(pos: inox.utils.Position, resSelect: Expr, outerEffect: Effect, effect: Effect): Expr = {
          val (cond, result) = select(pos, resSelect.getType, resSelect, outerEffect.path.toSeq)

          // We only overwrite the receiver when it is an actual mutable type.
          // This is necessary to handle immutable types being upcasted to `Any`, which is mutable.
          val assignment = if (isMutableType(effect.receiver.getType)) {
            val newValue = updatedTarget(effect.toTarget, Annotated(result, Seq(DropVCs)).setPos(pos))
            val adt = effect.receiver.getType
            val castedValue =
              if (adt.isInstanceOf[ADTType] && adt.asInstanceOf[ADTType].getSort.constructors.size == 1)
                newValue
              else
                Annotated(AsInstanceOf(newValue, effect.receiver.getType), Seq(DropVCs)).copiedFrom(newValue)
            Assignment(effect.receiver, castedValue).setPos(pos)
          } else UnitLiteral().setPos(pos)

          if (cond == BooleanLiteral(true)) assignment
          else IfExpr(cond, assignment, UnitLiteral().setPos(pos)).setPos(pos)
        }

        def mapApplication(formalArgs: Seq[ValDef], args: Seq[Expr], nfi: Expr, nfiType: Type, fiEffects: Set[Effect], env: Env): Expr = {
          if (fiEffects.exists(e => formalArgs contains e.receiver.toVal)) {
            val localEffects = (formalArgs zip args)
              .map { case (vd, arg) => (fiEffects.filter(_.receiver == vd.toVariable), arg) }
              .filter { case (effects, _) => effects.nonEmpty }
              .map { case (effects, arg) =>
                val rArg = freshenLocals(replaceFromSymbols(env.rewritings, arg))
                effects map (e => (e, e on rArg))
              }

            //TODO: The case f(A(x1,x1,x1)) could probably be handled by forbidding creation at any program point of
            //      case class with multiple refs as it is probably not useful

            val freshRes = ValDef(FreshIdentifier("res"), nfiType).copiedFrom(nfi)

            val extractResults = Block(
              for {
                (effects, index) <- localEffects.zipWithIndex
                (outerEffect0, innerEffects) <- effects
                effect0 <- innerEffects
              } yield {
                val outerEffect = outerEffect0.removeUnknownAccessor
                val effect = effect0.removeUnknownAccessor
                val pos = args(index).getPos
                val resSelect = TupleSelect(freshRes.toVariable, index + 2)

                makeAssignment(pos, resSelect, outerEffect, effect)
              },
              TupleSelect(freshRes.toVariable, 1))

            if (isMutableType(nfiType)) {
              LetVar(freshRes, nfi, transform(extractResults, env withBinding freshRes))
            } else {
              Let(freshRes, nfi, transform(extractResults, env))
            }
          } else {
            nfi
          }
        }

        // throws an exception if two arguments in the sequence share a target prefix
        private def checkAliasing(expr: Expr, args: Seq[Expr]): Unit = {
          val argTargets: Seq[((Expr, Set[Target]), Int)] =
            args.filter(arg => isMutableType(arg.getType))
              .map(arg => arg -> Try(getAllTargets(arg)).toOption
                .getOrElse(
                  exprOps.variablesOf(arg)
                    .filter(v => isMutableType(v.tpe))
                    .map(v => Target(v, None, Path.empty))
                )
              ).zipWithIndex

          for (((arg1, targets1), i) <- argTargets) {
            val otherTargets: Seq[(Expr, Set[Target])] = argTargets.filter(_._2 != i).map(_._1)
            for (target1 <- targets1)
              for ((arg2, targets2) <- otherTargets)
                for (target2 <- targets2)
                  if (target1.maybePrefixOf(target2) ||
                      target2.maybePrefixOf(target1))
                    throw MalformedStainlessCode(expr,
                      s"Illegal passing of aliased parameters ${arg1.asString} (with target: ${target1.asString}) " +
                      s"and ${arg2.asString} (with target: ${target2.asString})"
                    )
          }
        }

        override def transform(e: Expr, env: Env): Expr = (e match {
          case v: Variable if env.rewritings.contains(v.toVal) =>
            freshenLocals(env.rewritings(v.toVal))

          case ret @ Return(_) if freshLocals.isEmpty => super.transform(e, env)

          case ret @ Return(retExpr) =>
            Return(Tuple(transform(retExpr, env) +: freshLocals.map(_.setPos(ret))).setPos(ret)).setPos(ret)

          case swap @ Swap(array1, index1, array2, index2) =>
            val base = array1.getType.asInstanceOf[ArrayType].base
            val temp = ValDef.fresh("temp", base).setPos(swap)
            val ra1 = freshenLocals(replaceFromSymbols(env.rewritings, array1))
            val targets1 = getDirectTargets(ra1, ArrayAccessor(index1))
            val ra2 = freshenLocals(replaceFromSymbols(env.rewritings, array2))
            val targets2 = getDirectTargets(ra2, ArrayAccessor(index2))

            if (targets1.exists(target => !env.bindings.contains(target.receiver.toVal)))
              throw MalformedStainlessCode(swap, "Unsupported swap (first array)")

            if (targets2.exists(target => !env.bindings.contains(target.receiver.toVal)))
              throw MalformedStainlessCode(swap, "Unsupported swap (second array)")

            val updates1 =
              targets1.toSeq map { target =>
                val applied = updatedTarget(target, ArraySelect(array2, index2).setPos(swap))
                transform(Assignment(target.receiver, applied).setPos(swap), env)
              }
            val updates2 =
              targets2.toSeq map { target =>
                val applied = updatedTarget(target, temp.toVariable)
                transform(Assignment(target.receiver, applied).setPos(swap), env)
              }
            val updates = updates1 ++ updates2
            if (updates.isEmpty) UnitLiteral().setPos(swap)
            else
              Let(temp, transform(ArraySelect(array1, index1).setPos(swap), env),
                Block(updates.init, updates.last).setPos(swap)
              ).setPos(swap)

          case l @ Let(vd, e, b) if isMutableType(vd.tpe) =>
            // see https://github.com/epfl-lara/stainless/pull/920 for discussion

            val newExpr = transform(e, env)
            val targets = Try(getAllTargets(newExpr))

            if (targets.isSuccess) {
              // This branch handles all cases when targets can be precisely computed, namely when
              // 1. newExpr is a fresh expression
              // 2. newExpr is a precise alias to an existing variable
              val rewriting = targets.get.foldRight(vd.toVariable : Expr) {
                case (Target(r, Some(cond), path), rewriting) =>
                  val wrapped = path.wrap(r).getOrElse(
                    throw MalformedStainlessCode(l, "Unsupported `val` in AntiAliasing (conditional target)")
                  )
                  IfExpr(cond, wrapped, rewriting)
                case (Target(r, None, path), rewriting) =>
                  path.wrap(r).getOrElse(
                    throw MalformedStainlessCode(l, "Unsupported `val` in AntiAliasing (unconditional target)")
                  )
              }

              val newBody = transform(b, env withRewritings Map(vd -> rewriting) withBinding vd)
              LetVar(vd, newExpr, newBody).copiedFrom(l)

            } else if ((exprOps.variablesOf(e) & exprOps.variablesOf(b)).forall(v => !isMutableType(v.tpe))) {
              val newBody = transform(b, env withBinding vd)

              // for all effects of `b` whose receiver is `vd`
              val copyEffects = effects(b).filter(_.receiver == vd.toVariable).flatMap { eff =>

                // we apply the effect on the bound expression (after transformation)
                eff.on(newExpr).map { eff2 => makeAssignment(l.getPos, eff.receiver, eff, eff2) }
              }

              val resVd = ValDef.fresh("res", b.getType).copiedFrom(b)
              LetVar(
                vd, newExpr,
                Let(resVd, newBody, Block(copyEffects.toSeq, resVd.toVariable).copiedFrom(l)).copiedFrom(l)
              ).copiedFrom(l)

            } else {
              throw MalformedStainlessCode(l, "Unexpected `val` in AntiAliasing (couldn't compute targets and there are mutable variables shared between the binding and the body)")
            }

          case l @ LetVar(vd, e, b) if isMutableType(vd.tpe) =>
            val newExpr = transform(e, env)
            val newBody = transform(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case m @ MatchExpr(scrut, cses) if isMutableType(scrut.getType) =>
            if (effects(scrut).nonEmpty) {
              def liftEffects(e: Expr): (Seq[(ValDef, Expr)], Expr) = e match {
                case ArraySelect(e, i) if effects(i).nonEmpty =>
                  val (eBindings, eLift) = liftEffects(e)
                  val vd = ValDef(FreshIdentifier("index", true), Int32Type().copiedFrom(i)).copiedFrom(i)
                  (eBindings :+ (vd -> i), ArraySelect(eLift, vd.toVariable).copiedFrom(e))
                case _ if effects(e).nonEmpty =>
                  throw MalformedStainlessCode(m, "Unexpected effects in match scrutinee")
                case _ => (Seq.empty, e)
              }

              val (bindings, newScrut) = liftEffects(scrut)
              val newMatch = bindings.foldRight(MatchExpr(newScrut, cses).copiedFrom(m): Expr) {
                case ((vd, e), b) => Let(vd, e, b).copiedFrom(m)
              }
              transform(newMatch, env)
            } else {
              val newScrut = transform(scrut, env)
              val newCases = cses.map { case mc @ MatchCase(pattern, guard, rhs) =>
                val newRewritings =
                  mapForPattern(newScrut, pattern).view.filterKeys(v => isMutableType(v.getType)).toMap

                val newGuard = guard.map(transform(_, env withRewritings newRewritings))
                val newRhs = transform(rhs, env withRewritings newRewritings)
                MatchCase(pattern, newGuard, newRhs).copiedFrom(mc)
              }
              MatchExpr(newScrut, newCases).copiedFrom(m)
            }

          case up @ ArrayUpdate(a, i, v) =>
            val ra = freshenLocals(replaceFromSymbols(env.rewritings, a))
            val targets = getDirectTargets(ra, ArrayAccessor(i))

            if (targets.exists(target => !env.bindings.contains(target.receiver.toVal)))
              throw MalformedStainlessCode(up, "Unsupported form of array update")

            Block(targets.toSeq map { target =>
              val applied = updatedTarget(target, v)
              transform(Assignment(target.receiver, applied).copiedFrom(up), env)
            }, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case up @ MutableMapUpdate(map, k, v) =>
            val rmap = freshenLocals(replaceFromSymbols(env.rewritings, map))
            val targets = getDirectTargets(rmap, MutableMapAccessor(k))

            if (targets.exists(target => !env.bindings.contains(target.receiver.toVal)))
              throw MalformedStainlessCode(up, "Unsupported form of map update")

            Block(targets.toSeq map { target =>
              val applied = updatedTarget(target, v)
              transform(Assignment(target.receiver, applied).copiedFrom(up), env)
            }, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case as @ FieldAssignment(o, id, v) =>
            val so = freshenLocals(replaceFromSymbols(env.rewritings, o))
            val accessor = typeToAccessor(o.getType, id)
            val targets = getDirectTargets(so, accessor)

            if (targets.exists(target => !env.bindings.contains(target.receiver.toVal)))
              throw MalformedStainlessCode(as, "Unsupported form of field assignment")

            Block(targets.toSeq map { target =>
              val applied = updatedTarget(target, v)
              transform(Assignment(target.receiver, applied).copiedFrom(as), env)
            }, UnitLiteral().copiedFrom(as)).copiedFrom(as)

          // we need to replace local fundef by the new updated fun defs.
          case l @ LetRec(fds, body) =>
            val nfds = fds.map(fd => updateFunction(Inner(fd), env withLocals fds).toLocal)
            LetRec(nfds, transform(body, env withLocals fds)).copiedFrom(l)

          case e @ Ensuring(body, l @ Lambda(params, post)) =>
            Ensuring(transform(body, env), Lambda(params, transform(post, env)).copiedFrom(l)).copiedFrom(e)

          case l @ Lambda(params, body) =>
            val ft @ FunctionType(_, _) = l.getType
            val ownEffects = functionTypeEffects(ft)
            val aliasedParams: Seq[ValDef] = params.zipWithIndex.flatMap {
              case (vd, i) if ownEffects.contains(i) => Some(vd)
              case _ => None
            }

            if (aliasedParams.isEmpty) {
              Lambda(params, transform(body, env)).copiedFrom(l)
            } else {
              val freshLocals = aliasedParams.map(v => v.freshen)
              val rewritingMap = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap
              val freshBody = exprOps.replaceFromSymbols(rewritingMap, body)

              //WARNING: only works if side effects in Tuples are extracted from left to right,
              //         in the ImperativeTransformation phase.
              val finalBody: Expr = Tuple(freshBody +: freshLocals.map(_.toVariable))

              val wrappedBody: Expr = freshLocals.zip(aliasedParams).foldLeft(finalBody) {
                (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(bd)
              }
              Lambda(params, transform(wrappedBody, env)).copiedFrom(l)
            }

          case fi @ FunctionInvocation(id, tps, args) =>
            val fd = Outer(fi.tfd.fd)
            val rewrittenArgs = args.map(arg =>
              freshenLocals(replaceFromSymbols(
                env.rewritings.view.mapValues(e => Annotated(e, Seq(DropVCs)).setPos(e)).toMap,
                arg
              )))
            if (!fi.tfd.flags.exists(_.name == "accessor") && !fi.tfd.flags.contains(IsPure))
              checkAliasing(fi, rewrittenArgs)

            val nfi = FunctionInvocation(
              id, tps, rewrittenArgs.map(transform(_, env))
            ).copiedFrom(fi)

            mapApplication(fd.params, args, nfi, fi.tfd.instantiate(analysis.getReturnType(fd)), effects(fd), env)

          case alr @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val fd = Inner(env.locals(id))
            val rewrittenArgs = args.map(arg => freshenLocals(replaceFromSymbols(env.rewritings, arg)))
            checkAliasing(alr, rewrittenArgs)

            val vis: Set[Variable] = varsInScope(fd)
            rewrittenArgs.flatMap(exprOps.variablesOf(_)).find(vis contains _)
              .foreach(v => context.reporter.fatalError(alr.getPos, "Illegal passing of aliased local variable: " + v))

            val nfi = ApplyLetRec(
              id, tparams,
              FunctionType(fd.params.map(_.getType), analysis.getReturnType(fd)).copiedFrom(tpe), tps,
              rewrittenArgs.map(transform(_, env))
            ).copiedFrom(alr)

            val resultType = typeOps.instantiateType(analysis.getReturnType(fd), (tparams zip tps).toMap)
            mapApplication(fd.params, args, nfi, resultType, effects(fd), env)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType
            val ftEffects = functionTypeEffects(ft)
            if (ftEffects.nonEmpty) {
              val rewrittenArgs = args.map(arg => freshenLocals(replaceFromSymbols(env.rewritings, arg)))
              checkAliasing(app, rewrittenArgs)
              val nfi = Application(
                transform(callee, env),
                rewrittenArgs.map(transform(_, env))
              ).copiedFrom(app)

              val params = from.map(tpe => ValDef.fresh("x", tpe))
              val appEffects = params.zipWithIndex.collect {
                case (vd, i) if ftEffects(i) => ModifyingEffect(vd.toVariable, Path.empty)
              }
              val to = makeFunctionTypeExplicit(ft).asInstanceOf[FunctionType].to
              mapApplication(params, args, nfi, to, appEffects.toSet, env)
            } else {
              Application(transform(callee, env), args.map(transform(_, env))).copiedFrom(app)
            }

          case Operator(es, recons) => recons(es.map(transform(_, env)))
        }).copiedFrom(e)
      }

      val transformer = new TransformerImpl(self.s, self.t)
      transformer.transform(body, env)
    }

    //for each fun def, all the vars the the body captures.
    //Only mutable types.
    def varsInScope(fd: FunAbstraction): Set[Variable] = {
      val allFreeVars = exprOps.variablesOf(fd.fullBody)
      val freeVars = allFreeVars -- fd.params.map(_.toVariable)
      freeVars.filter(v => isMutableType(v.tpe))
    }

    // Given a receiver object (mutable class, array or map, usually as a reference id),
    // and a path of field/index access, build a copy of the original object, with
    // properly updated values
    def updatedTarget(target: Target, newValue: Expr): Expr = {
      def rec(receiver: Expr, path: Seq[Accessor]): Expr = path match {
        case ADTFieldAccessor(id) :: fs =>
          val adt @ ADTType(_, tps) = receiver.getType
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
            throw FatalError(s"Could find class for type ${receiver.getType}")
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
          val tt @ TupleType(_) = receiver.getType
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

        case Target(receiver, Some(condition), path) if effects(condition).nonEmpty =>
          throw MalformedStainlessCode(condition, s"Effects are not allowed in condition of effects: ${condition.asString}")

        case Target(receiver, Some(condition), path) =>
          Annotated(
            AsInstanceOf(
              IfExpr(
                condition.setPos(newValue),
                rec(receiver, path.toSeq),
                receiver
              ).copiedFrom(newValue),
              receiver.getType
            ).copiedFrom(newValue),
            Seq(DropVCs)
          ).copiedFrom(newValue)
      }
    }

    Some(transformer.transform(updateFunction(Outer(fd), Environment.empty).toFun))
  }

  override protected def extractSort(analysis: SymbolsAnalysis, sort: ADTSort): ADTSort =
    analysis.transformer.transform(sort)

  override protected def extractClass(analysis: SymbolsAnalysis, cd: ClassDef): ClassDef =
    analysis.transformer.transform(cd)
}

object AntiAliasing {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends AntiAliasing(s)(t)
    new Impl(trees, trees)
  }
}
