/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

trait AntiAliasing
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with EffectsAnalyzer
     with EffectsChecker
     with GhostChecker { self =>
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    getDependencyKey(fd.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult]((sort, context) =>
    getDependencyKey(sort.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult]((cd, context) =>
    getDependencyKey(cd.id)(context.symbols)
  )

  override protected type FunctionResult = Option[FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected case class SymbolsAnalysis(symbols: Symbols) extends EffectsAnalysis {
    import symbols._

    // Convert a function type with mutable parameters, into a function type
    // that returns the mutable parameters. This makes explicit all possible
    // effects of the function. This should be used for higher order functions
    // declared as parameters.
    def makeFunctionTypeExplicit(tpe: Type): Type = tpe match {
      case ft @ FunctionType(from, to) =>
        ft.copy(to = tupleTypeWrap(to +: from.filter(isMutableType)).copiedFrom(to)).copiedFrom(tpe)
      case pt @ PiType(params, to) =>
        pt.copy(to = tupleTypeWrap(to +: params.map(_.tpe).filter(isMutableType)).copiedFrom(to)).copiedFrom(tpe)
    }

    object transformer extends SelfTreeTransformer {

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
  override protected def getContext(symbols: Symbols) = SymbolsAnalysis(symbols)

  override protected def extractFunction(analysis: SymbolsAnalysis, fd: FunDef): Option[FunDef] = {
    import analysis._
    import symbols._

    checkGhost(fd)(analysis)

    checkEffects(fd)(analysis) match {
      case CheckResult.Ok => ()
      case CheckResult.Skip => return None
      case CheckResult.Error(err) => throw err
    }

    type Environment = (Set[ValDef], Map[ValDef, Expr], Map[Identifier, LocalFunDef])
    implicit class EnvWrapper(env: Environment) {
      val (bindings, rewritings, locals) = env
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
        override val s: self.s.type = self.s
        override val t: self.t.type = self.t
        override type Env = Environment

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
              val aliased = effects.tails.flatMap {
                case e1 +: es => es.collect { case e2 if (e1 prefixOf e2) || (e2 prefixOf e1) => (e1, e2) }
                case Nil => Nil
              }

              if (aliased.nonEmpty) {
                val (e1, _) = aliased.next
                throw MalformedStainlessCode(e1.receiver, "Illegal passing of aliased parameter")
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
                  case (adt: ADTType, ADTFieldAccessor(id) +: xs) =>
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

                  case (ct: ClassType, ClassFieldAccessor(id) +: xs) =>
                    val field = getClassField(ct, id).get
                    val fieldClassType = classForField(ct, id).get.toType
                    val condition = IsInstanceOf(expr, fieldClassType).setPos(pos)

                    val (recCond, recSelect) = select(field.tpe, ClassSelector(AsInstanceOf(expr, fieldClassType).setPos(expr), id).setPos(pos), xs)
                    (and(condition, recCond), recSelect)

                  case (ArrayType(base), ArrayAccessor(idx) +: xs) =>
                    select(base, ArraySelect(expr, idx).setPos(pos), xs)

                  case (MutableMapType(from, to), MutableMapAccessor(idx) +: xs) =>
                    select(to, MutableMapApply(expr, idx).setPos(pos), xs)

                  case (_, Nil) => (BooleanLiteral(true).setPos(pos), expr)
                }

                val (cond, result) = select(resSelect.getType, resSelect, outerEffect.path.toSeq)

                // We only overwrite the receiver when it is an actual mutable type.
                // This is necessary to handle immutable types being upcasted to `Any`, which is mutable.
                val assignment = if (isMutableType(effect.receiver.getType)) {
                  val newValue = applyEffect(effect.toTarget, Annotated(result, Seq(Unchecked)).setPos(pos))
                  val castedValue = Annotated(AsInstanceOf(newValue, effect.receiver.getType), Seq(Unchecked))
                  Assignment(effect.receiver, castedValue).setPos(args(index))
                } else UnitLiteral().setPos(pos)

                if (cond == BooleanLiteral(true)) assignment
                else IfExpr(cond, assignment, UnitLiteral().setPos(pos)).setPos(pos)
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

        override def transform(e: Expr, env: Env): Expr = (e match {
          case l @ Let(vd, e, b) if isMutableType(vd.tpe) =>
            val newExpr = transform(e, env)
            if (getKnownEffects(newExpr).nonEmpty) {
              val newBody = transform(b, env withRewritings Map(vd -> newExpr))
              Let(vd, newExpr, newBody).copiedFrom(l)
            } else {
              val newBody = transform(b, env withBinding vd)
              LetVar(vd, newExpr, newBody).copiedFrom(l)
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
                val newRewritings = mapForPattern(newScrut, pattern)
                val newGuard = guard.map(transform(_, env withRewritings newRewritings))
                val newRhs = transform(rhs, env withRewritings newRewritings)
                MatchCase(pattern, newGuard, newRhs).copiedFrom(mc)
              }
              MatchExpr(newScrut, newCases).copiedFrom(m)
            }

          case up @ ArrayUpdate(a, i, v) =>
            val ra = exprOps.replaceFromSymbols(env.rewritings, a)
            val effects = getExactEffects(ra)

            if (effects.exists(eff => !env.bindings.contains(eff.receiver.toVal)))
              throw MalformedStainlessCode(up, "Unsupported form of array update")

            Block(effects.toSeq map { effect =>
              val applied = applyEffect(effect + ArrayAccessor(i), v)
              transform(Assignment(effect.receiver, applied).copiedFrom(up), env)
            }, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case up @ MutableMapUpdate(map, k, v) =>
            val rmap = exprOps.replaceFromSymbols(env.rewritings, map)
            val effects = getExactEffects(rmap)

            if (effects.exists(eff => !env.bindings.contains(eff.receiver.toVal)))
              throw MalformedStainlessCode(up, "Unsupported form of map update")

            Block(effects.toSeq map { effect =>
              val applied = applyEffect(effect + MutableMapAccessor(k), v)
              transform(Assignment(effect.receiver, applied).copiedFrom(up), env)
            }, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case as @ FieldAssignment(o, id, v) =>
            val so = exprOps.replaceFromSymbols(env.rewritings, o)
            val effects = getExactEffects(so)

            if (effects.exists(eff => !env.bindings.contains(eff.receiver.toVal)))
              throw MalformedStainlessCode(as, "Unsupported form of field assignment")

            val accessor = typeToAccessor(o.getType, id)

            Block(effects.toSeq map { effect =>
              val applied = applyEffect(effect + accessor, v)
              transform(Assignment(effect.receiver, applied).copiedFrom(as), env)
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
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = FunctionInvocation(
              id, tps, args.map(arg => transform(exprOps.replaceFromSymbols(env.rewritings, arg), env))
            ).copiedFrom(fi)

            mapApplication(fd.params, args, nfi, fi.tfd.instantiate(analysis.getReturnType(fd)), effects(fd), env)

          case alr @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val fd = Inner(env.locals(id))
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = ApplyLetRec(
              id, tparams,
              FunctionType(fd.params.map(_.getType), analysis.getReturnType(fd)).copiedFrom(tpe), tps,
              args.map(arg => transform(exprOps.replaceFromSymbols(env.rewritings, arg), env))
            ).copiedFrom(alr)

            val resultType = typeOps.instantiateType(analysis.getReturnType(fd), (tparams zip tps).toMap)
            mapApplication(fd.params, args, nfi, resultType, effects(fd), env)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(from, to) = callee.getType
            val ftEffects = functionTypeEffects(ft)
            if (ftEffects.nonEmpty) {
              val nfi = Application(
                transform(callee, env),
                args.map(arg => transform(exprOps.replaceFromSymbols(env.rewritings, arg), env))
              ).copiedFrom(app)

              val params = from.map(tpe => ValDef.fresh("x", tpe))
              val appEffects = params.zipWithIndex.collect { case (vd, i) if ftEffects(i) => Effect(vd.toVariable, Path.empty) }
              val to = makeFunctionTypeExplicit(ft).asInstanceOf[FunctionType].to
              mapApplication(params, args, nfi, to, appEffects.toSet, env)
            } else {
              Application(transform(callee, env), args.map(transform(_, env))).copiedFrom(app)
            }

          case cs @ ClassSelector(obj, sel) =>
            ClassSelector(
              transform(exprOps.replaceFromSymbols(env.rewritings, obj), env),
              sel
            ).copiedFrom(cs)

          case as @ ADTSelector(adt, sel) =>
            ADTSelector(
              transform(exprOps.replaceFromSymbols(env.rewritings, adt), env),
              sel
            ).copiedFrom(as)

          case Operator(es, recons) => recons(es.map(transform(_, env)))
        }).copiedFrom(e)
      }

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
    def applyEffect(effect: Target, newValue: Expr): Expr = {
      def rec(receiver: Expr, path: Seq[Accessor]): Expr = path match {
        case ADTFieldAccessor(id) :: fs =>
          val adt @ ADTType(_, tps) = receiver.getType
          val tcons = adt.getSort.constructors.find(_.fields.exists(_.id == id)).get
          val r = rec(Annotated(ADTSelector(receiver, id).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)

          ADT(tcons.id, tps, tcons.definition.fields.map { vd =>
            if (vd.id == id) r
            else Annotated(ADTSelector(receiver, vd.id).copiedFrom(receiver), Seq(Unchecked)).copiedFrom(receiver)
          }).copiedFrom(newValue)

        case ClassFieldAccessor(id) :: fs =>
          val optCd = receiver.getType match {
            case ct: ClassType => classForField(ct, id)
            case tp => throw FatalError(s"Cannot apply ClassFieldAccessor to type $tp")
          }

          val (cd, ct) = optCd.map(cd => (cd, cd.toType)).getOrElse {
            throw FatalError(s"Could find class for type ${receiver.getType}")
          }

          val casted = AsInstanceOf(receiver, cd.toType).copiedFrom(receiver)
          val r = rec(Annotated(ClassSelector(casted, id).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)

          ClassConstructor(ct, ct.tcd.fields.map { vd =>
            if (vd.id == id) r
            else Annotated(ClassSelector(casted, vd.id).copiedFrom(receiver), Seq(Unchecked)).copiedFrom(receiver)
          }).copiedFrom(newValue)

        case ArrayAccessor(index) :: fs =>
          val r = rec(Annotated(ArraySelect(receiver, index).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)
          ArrayUpdated(receiver, index, r).copiedFrom(newValue)

        case MutableMapAccessor(index) :: fs =>
          val r = rec(Annotated(MutableMapApply(receiver, index).copiedFrom(newValue), Seq(Unchecked)).copiedFrom(newValue), fs)
          MutableMapUpdated(receiver, index, r).copiedFrom(newValue)

        case Nil => newValue
      }

      effect match {
        case Target(receiver, None, path) =>
          rec(receiver, path.toSeq)

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
          Seq(Unchecked)
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
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new AntiAliasing {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
