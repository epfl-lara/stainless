/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

import scala.util.{Failure, Success, Try}

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
  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, (SortResult, SortSummary)]((sort, context) =>
    getDependencyKey(sort.id)(using context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]((cd, context) =>
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

  enum FunctionSummary {
    case Untransformed(fid: Identifier)
    case Transformed(fid: Identifier)
  }
  override protected def extractFunction(analysis: SymbolsAnalysis, fd: FunDef): (Option[FunDef], FunctionSummary) = {
    import analysis.{given, _}
    import symbols._

    checkGhost(fd)(analysis)

    checkEffects(fd)(analysis) match {
      case CheckResult.Ok => ()
      case CheckResult.Skip => return (None, FunctionSummary.Untransformed(fd.id))
      case CheckResult.Error(err) => throw err
    }

    type Environment = (Set[ValDef], Map[ValDef, Set[Target]], Map[Identifier, LocalFunDef])
    extension (env: Environment) {
      def bindings: Set[ValDef] = env._1
      def targets: Map[ValDef, Set[Target]] = env._2
      def locals: Map[Identifier, LocalFunDef] = env._3
      def withBinding(vd: ValDef): Environment = (bindings + vd, targets, locals)
      def withBindings(vds: Iterable[ValDef]): Environment = (bindings ++ vds, targets, locals)
      def withTargets(vd: ValDef, tgs: Set[Target]): Environment = (bindings, targets + (vd -> tgs), locals)
      def withLocals(fds: Seq[LocalFunDef]): Environment = (bindings, targets, locals ++ fds.map(fd => fd.id -> fd))
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

        // Utility function that essentially create an expression representing the update of `target` with `resSelect`
        // For instance, if we would like to update the target v.a.b.c (with condition `cond`) with `newC`,
        // this function would return the following expression:
        //   if (cond) {
        //     v = A(
        //       B(
        //         newC,
        //         v.a.b.otherFields), // Other fields of v.a.b, unaffected by the update, and are just copied
        //       v.a.otherFields) // Ditto
        //   }
        // Note: in general, such assignment may generate VCs (e.g. index in bound for array update).
        // However, in the case of translating side effects of function as variable assignments (done in mapApplication),
        // it is safe to to @DropVCs the assignment, as the correctness of mutation is discharged to
        // the called function, not the callee.
        def makeAssignment(pos: inox.utils.Position, resSelect: Expr, outerPath: Seq[Accessor], target: Target, dropVcs: Boolean = false): Expr = {
          def wrap(e: Expr): Expr = {
            if (dropVcs) Annotated(e, Seq(DropVCs)).copiedFrom(e)
            else e
          }

          val (cond, result) = select(pos, resSelect.getType, resSelect, outerPath)
          val combinedCond = andJoin(cond +: target.condition.toSeq)

          // We only overwrite the receiver when it is an actual mutable type.
          // This is necessary to handle immutable types being upcasted to `Any`, which is mutable.
          if (combinedCond != BooleanLiteral(false) && isMutableType(target.receiver.getType)) {
            val newValue = updatedTarget(target.copy(condition = Some(combinedCond)), wrap(result))
            val adt = target.receiver.getType
            val castedValue =
              if (adt.isInstanceOf[ADTType] && adt.asInstanceOf[ADTType].getSort.constructors.size == 1)
                newValue
              else
                wrap(AsInstanceOf(newValue, target.receiver.getType).copiedFrom(newValue))
            Assignment(target.receiver, castedValue).setPos(pos)
          } else {
            UnitLiteral().setPos(pos)
          }
        }

        // NOTE: `args` must refer to the arguments of the function invocation before transformation (the original args)
        def mapApplication(formalArgs: Seq[ValDef], args: Seq[Expr], nfi: Expr, nfiType: Type, fiEffects: Set[Effect], env: Env): Expr = {
          if (fiEffects.exists(e => formalArgs contains e.receiver.toVal)) {
            val localEffects: Seq[Set[(Effect, Set[(Effect, Option[Expr])])]] = (formalArgs zip args)
              .map { case (vd, arg) => (fiEffects.filter(_.receiver == vd.toVariable), arg) }
              .filter { case (effects, _) => effects.nonEmpty }
              .map { case (effects, arg) => effects map (e => (e, e on arg)) }

            val freshRes = ValDef(FreshIdentifier("res"), nfiType).copiedFrom(nfi)

            val assgns = (for {
              (effects, index) <- localEffects.zipWithIndex
              (outerEffect0, innerEffects) <- effects
              (effect0, effectCond) <- innerEffects
            } yield {
              val outerEffect = outerEffect0.removeUnknownAccessor
              val effect = effect0.removeUnknownAccessor
              val pos = args(index).getPos
              val resSelect = TupleSelect(freshRes.toVariable, index + 2)
              // Follow all aliases of the updated target (may include self if it has no alias)
              val primaryTargs = dealiasTarget(effect.toTarget(effectCond), env)
              val assignedPrimaryTargs = primaryTargs.toSeq
                .map(t => makeAssignment(pos, resSelect, outerEffect.path.path, t, dropVcs = true))
              val updAliasingValDefs = updatedAliasingValDefs(primaryTargs, env, pos)

              assignedPrimaryTargs ++ updAliasingValDefs
            }).flatten
            val extractResults = Block(assgns, TupleSelect(freshRes.toVariable, 1))

            if (isMutableType(nfiType)) {
              LetVar(freshRes, nfi, extractResults)
            } else {
              Let(freshRes, nfi, extractResults)
            }
          } else {
            nfi
          }
        }

        def unordPairs[A](as: Seq[A]): Seq[(A, A)] = {
          for {
            (a1, i1) <- as.zipWithIndex
            a2 <- as.drop(i1 + 1)
          } yield (a1, a2)
        }

        // Given an expression e, collect "all" mutable targets that are of the form v.a.b.c
        // For instance, if we have:
        //    case class A(val left: B, val right: B)
        //    case class B(var c1: C, var c2: C)
        //    case class C(var x: Int)
        //    val res: (Unit, A) = ...
        //    A(B(res._2.left.c1, a.left.c2), a.right)
        // collectTargetsForAliasing on the last expression would give us:
        //    Target(res, None, ._2.left.c1),
        //    Target(a, None, .left.c2)
        //    Target(a, None, .right)
        //
        // Note: contrarily to getAllTargets, we return here a Seq[Target], as we would like to keep duplicates.
        // For instance, assuming v.field is of a mutable type, collectTargetsForAliasing on the expression
        // (v.field, v.field) would yield Seq(Target(v, None, .field), Target(v, None, .field)), which would
        // be flagged as illegal because v.field is aliased.
        def collectTargetsForAliasing(e: Expr, env: Env): Seq[Target] = {
          var result = Seq.empty[Target]
          object collector extends ConcreteOOSelfTreeTraverser {
            override def traverse(e: Expr): Unit = e match {
              case ADT(id, tps, args) =>
                args.foreach(traverse)

              case ClassConstructor(_, args) =>
                args.foreach(traverse)

              case Tuple(exprs) =>
                exprs.foreach(traverse)

              case FiniteArray(elems, _) =>
                elems.foreach(traverse)

              case ArrayUpdated(arr, _, arg) =>
                traverse(arr)
                // i is of immutable type, so there can't be targets
                traverse(arg)

              case MapUpdated(map, _, v) =>
                traverse(map)
                // Same for the key
                traverse(v)

              case _ =>
                result ++= getAllTargetsDealiased(e, env)
                  .getOrElse(throw MalformedStainlessCode(e, s"Possible aliasing within ${e.asString} (could not compute precise targets)"))
            }
          }

          collector.traverse(e)
          result
        }

        // throws an exception if two arguments in the sequence share a target prefix
        def checkAliasing(expr: Expr, args: Seq[Expr], env: Env): Unit = {
          val argTargets: Seq[(Expr, Seq[Target])] =
            args.filter(arg => isMutableType(arg.getType))
              .map(arg => arg -> collectTargetsForAliasing(arg, env))

          for (((arg1, targets1), (arg2, targets2)) <- unordPairs(argTargets)) {
            for (target1 <- targets1; target2 <- targets2) {
              if (target1.maybePrefixOf(target2) || target2.maybePrefixOf(target1))
                throw MalformedStainlessCode(expr,
                  s"Illegal passing of aliased parameters ${arg1.asString} (with target: ${target1.asString}) " +
                    s"and ${arg2.asString} (with target: ${target2.asString})")
            }
          }
        }

        def getAllTargetsDealiased(e: Expr, env: Env): Option[Set[Target]] = getTargetsDealiased(e, ModifyingKind, Seq.empty, env)

        def getDirectTargetsDealiased(e: Expr, accessor: Accessor, env: Env): Option[Set[Target]] = getTargetsDealiased(e, ReplacementKind, Seq(accessor), env)

        // Like `getTargets`, but de-aliasing the resulting targets (see dealiasTarget)
        def getTargetsDealiased(e: Expr, kind: EffectKind, path: Seq[Accessor], env: Env): Option[Set[Target]] =
          Try(getTargets(e, kind, path)).toOption.map(dealiasTargets(_, env))

        // Return the set of targets that `target` is aliasing.
        // Example:
        //   Assuming env.targets =
        //     x -> (cond1, a.b.c), (cond2, d.e.f)
        //     y -> (cond3, g.h)
        //   where cond1,2,3 are the condition of the targets.
        //   Then dealiasTarget of:
        //     - l.m.n would return l.m.n itself (along with its condition).
        //     - x.o.p with condition cond4 would return both:
        //         * a.b.c.o.p with condition cond1 && cond4
        //         * d.e.f.o.p with condition cond2 && cond4
        def dealiasTarget(target: Target, env: Env): Set[Target] = {
          env.targets.find(_._1.toVariable == target.receiver).map {
            case (_, existingTargets: Set[Target]) =>
              val res = existingTargets.map(_.append(target))
              if (res.isEmpty) Set(target)
              else res
          }.getOrElse(Set(target))
        }

        def dealiasTargets(targets: Set[Target], env: Env): Set[Target] = {
          val dealiased = targets.flatMap(dealiasTarget(_, env))
          groupedTargets(dealiased)
        }

        // Group targets that have the same receiver and path under one target (by or'ing their condition)
        def groupedTargets(targets: Set[Target]): Set[Target] = {
          targets.groupBy(t => (t.receiver, t.path))
            .map { case ((recv, path), tgs) =>
              val cond = simplifyOr(tgs.map(_.condition.getOrElse(BooleanLiteral(true))).toSeq)
              Target(recv, Some(cond), path)
            }.toSet
        }

        // All bindings that may refer to a proper prefix of the given `updTarget`.
        // Example:
        //   Assuming env.targets =
        //     x -> (cond1, a.b.c), (cond2, d.e.f)
        //     y -> (cond3, g.h), (cond4, a.b.c.d)
        //   aliasingValDefs on a.b would return x -> (cond1, a.b.c), y -> (cond4, a.b.c.d)
        //   On the other hand, aliasingValDefs on a.b.c would only return y -> (cond4, a.b.c.d)
        //   (as a.b.c is not a *proper* prefix of itself)
        def aliasingValDefs(updTarget: Target, env: Env): Map[ValDef, Set[Target]] = {
          env.targets.map {
            case (vd, candidatePrefixes) =>
              val properPrefixes = candidatePrefixes.filter(_.maybeProperPrefixOf(updTarget))
              vd -> properPrefixes
          }.filter(_._2.nonEmpty)
        }

        def aliasingValDefs(updTargets: Set[Target], env: Env): Map[ValDef, Set[Target]] = {
          updTargets.flatMap(aliasingValDefs(_, env))
            .groupBy(_._1)
            .map {
              case (vd, targss) => vd -> groupedTargets(targss.flatMap(_._2))
            }
        }

        // Create expressions that represent the re-assignment of the aliases w.r.t. their targets.
        // For instance, if we take the env.targets from the example above, then calling
        // updatedAliasingValDefs on (cond5, a.b.c.d.e) would return:
        //    if (cond1) x = a.b.c else ()
        //    if (cond4) y = a.b.c.d else ()
        // (note that we do not make use of the condition of the given targets such as cond5; here, we are interested
        // in "refreshing" the bindings. If the underlying value didn't change, "refreshing" would be useless but not incorrect)
        def updatedAliasingValDefs(targets: Set[Target], env: Env, pos: inox.utils.Position): Seq[Expr] = {
          val aliases = aliasingValDefs(targets, env)
          aliases.toSeq.flatMap {
            case (vd, prefixes) =>
              prefixes.map { properPrefix =>
                makeAssignment(pos, properPrefix.wrap.get, Seq.empty, Target(vd.toVariable, properPrefix.condition, Path.empty))
              }
          }
        }

        // Create expressions representing the update of the given `targets` with `newValue`, as well as the update of their aliases.
        def updatedTargetsAndAliases(targets: Set[Target], newValue: Expr, env: Env, pos: inox.utils.Position): Seq[Expr] = {
          val primaryAssignments = targets.toSeq.map(makeAssignment(pos, newValue, Seq.empty, _))
          val aliasesUpdates = updatedAliasingValDefs(targets, env, pos)
          primaryAssignments ++ aliasesUpdates
        }

        override def transform(e: Expr, env: Env): Expr = (e match {
          case ret @ Return(_) if freshLocals.isEmpty => super.transform(e, env)

          case ret @ Return(retExpr) =>
            Return(Tuple(transform(retExpr, env) +: freshLocals.map(_.setPos(ret))).setPos(ret)).setPos(ret)

          case swap @ Swap(array1, index1, array2, index2) =>
            // Though `array1`, `index1`, `array2` and `index2` are all normalized, we still need to recursively transform
            // them, as they can refer to constructs that needs transformation, such as lambdas that mutate their params
            // (e.g. `Array(SomeClass((x: Box) => x.value += 1))` is normalized, but we need to transform the inner lambda
            // to get `Array(SomeClass((x: Box) => ((), Box(x.value + 1))))`).
            assertReferentiallyTransparent(index1)
            assertReferentiallyTransparent(index2)

            val recArray1 = transform(array1, env)
            val recArray2 = transform(array2, env)
            val recIndex1 = transform(index1, env)
            val recIndex2 = transform(index2, env)

            val base = recArray1.getType.asInstanceOf[ArrayType].base
            val temp = ValDef.fresh("temp", base).setPos(swap)
            val targets1 = getDirectTargetsDealiased(recArray1, ArrayAccessor(recIndex1), env)
              .getOrElse(throw MalformedStainlessCode(swap, "Unsupported swap (first array)"))
            val targets2 = getDirectTargetsDealiased(recArray2, ArrayAccessor(recIndex2), env)
              .getOrElse(throw MalformedStainlessCode(swap, "Unsupported swap (second array)"))

            val updates1 = updatedTargetsAndAliases(targets1, ArraySelect(recArray2, recIndex2).setPos(swap), env, swap.getPos)
            val updates2 = updatedTargetsAndAliases(targets2, temp.toVariable, env, swap.getPos)
            val updates = updates1 ++ updates2
            if (updates.isEmpty) UnitLiteral().setPos(swap)
            else
              Let(temp, transform(ArraySelect(recArray1, recIndex1).setPos(swap), env),
                Block(updates.init, updates.last).setPos(swap)
              ).setPos(swap)

          case cellSwap @ CellSwap(cell1, cell2) =>
            // Though `cell1`, `cell2` are all normalized, we still need to recursively transform
            // them, as they can refer to constructs that needs transformation, such as lambdas that mutate their params
            val recCell1 = transform(cell1, env)
            val recCell2 = transform(cell2, env)

            val base = recCell1.getType.asInstanceOf[ClassType].tps.head

            val cellClassDef = symbols.lookup.get[ClassDef]("stainless.lang.Cell").get
            val vFieldId = cellClassDef.fields.head.id

            val temp = ValDef.fresh("temp", base).setPos(cellSwap)
            val targets1 = getDirectTargetsDealiased(recCell1, ClassFieldAccessor(vFieldId), env)
              .getOrElse(throw MalformedStainlessCode(cellSwap, "Unsupported cellSwap (first cell)"))
            val targets2 = getDirectTargetsDealiased(recCell2, ClassFieldAccessor(vFieldId), env)
              .getOrElse(throw MalformedStainlessCode(cellSwap, "Unsupported cellSwap (second cell)"))

            val updates1 = updatedTargetsAndAliases(targets2, ClassSelector(cell1, vFieldId).setPos(cellSwap), env, cellSwap.getPos)
            val updates2 = updatedTargetsAndAliases(targets1, temp.toVariable, env, cellSwap.getPos)
            val updates = updates1 ++ updates2
            if (updates.isEmpty) UnitLiteral().setPos(cellSwap)
            else
              Let(temp, transform(ClassSelector(recCell2, vFieldId).setPos(cellSwap), env),
                Block(updates.init, updates.last).setPos(cellSwap)
              ).setPos(cellSwap)

          case l @ Let(vd, e, b) if isMutableType(vd.tpe) =>
            // see https://github.com/epfl-lara/stainless/pull/920 for discussion

            val newExpr = transform(e, env)
            val targets = getAllTargetsDealiased(newExpr, env)
            targets match {
              case Some(targets) =>
                // This branch handles all cases when targets can be precisely computed, namely when
                // 1. newExpr is a fresh expression
                // 2. newExpr is a precise alias to existing variable(s)
                // 3. A combination of 1. and 2. (e.g. val y = if (cond) x else Ref(123))

                // Targets with a false condition are those that are never accessed, we can remove them.
                val targs = targets.filterNot(_.condition == Some(BooleanLiteral(false)))
                // If there are more than one target, then it must be the case that their conditions are all disjoint,
                // due to the way they are computed by `getTargets`.
                // (here, we use a weaker prop. that asserts that all their condition are defined, for sanity checks)
                assert(targs.size <= 1 || targs.forall(_.condition.isDefined))

                // extraTarget: whether we should treat `vd` as a new target or not.
                val extraTarget = {
                  if (targs.isEmpty) {
                    // newExpr is a fresh expression (case 1), so `vd` is introducing a new target.
                    Seq(Target(vd.toVariable, None, Path.empty))
                  } else if (targs.size == 1 && targs.head.condition.isEmpty) {
                    // newExpr is a precise and unconditional alias to an existing variable - no new targets (case 2).
                    Seq.empty[Target]
                  } else {
                    // Here, we have >= 1 targets and all of them are conditional:
                    //   cond1 -> target1
                    //   ...
                    //   condn -> targetn
                    // If cond1 && ... && condn provably cover all possible cases, then we know that `newExpr` is
                    // a precise alias to n existing variables, so there are no new targets to consider (case 2).
                    // Otherwise, it may be the case that `newExpr` refer to fresh expression and alias existing variables (case 3),
                    // such as in the following example:
                    //   val y = if (cond1) x else Ref(123)
                    // Here, the targets of `y` would be the targets of x, with condition cond1.
                    // But it also conditionally introduce a new target, namely Ref(123) when !cond1.
                    // In such case, we introduce `y` as a new target, with condition !cond1.
                    assert(targs.forall(_.condition.isDefined))
                    val disj = simplifyOr(targs.map(_.condition.get).toSeq)
                    val negatedConds = simpleNot(disj)
                    if (negatedConds == BooleanLiteral(false)) Seq.empty[Target]
                    else Seq(Target(vd.toVariable, Some(negatedConds), Path.empty))
                  }
                }

                val newBody = transform(b, env.withTargets(vd, targs ++ extraTarget).withBinding(vd))
                // Note: even though there are no effects on `vd`, we still need to re-assign it
                // in case it aliases a target that gets updated.
                // As such, we use appearsInAssignment (on the transformed body) instead of checking for effects (on the original body)
                val canLetVal = !appearsInAssignment(vd.toVariable, newBody)
                if (canLetVal) Let(vd, newExpr, newBody).copiedFrom(l)
                else LetVar(vd, newExpr, newBody).copiedFrom(l)
              case None =>
                // In this scenario, where we cannot precisely compute the targets of `e`, we can observe that
                // if the (dealiased) variables appearing in `e` and those appearing in `b` (dealiased as well)
                // are disjoint, then we can be sure that `b` will not *directly* modify the variables in `e`.
                // On the other hand, `b` is of course allowed to modify `vd`, for which we must
                // apply the effects afterwards (represented below as `copyEffects`).
                //
                // We can further refine this observation by noting that (dealised) variables in `e` *may* appear
                // in `b` as well as long as they are not constituting the evaluation result of `e`, or in other
                // terms, that they do not appear in a terminal position, which is recursively define as follows:
                //   -Terminal of let v = e in b is the terminal in b
                //   -Terminal of v is v itself
                //   -Terminals of if (b) e1 else e2 is terminals of e1 and e2
                //   -and so on
                // Indeed, these occurrences will properly be updated by the recursive transformation.
                // The test `imperative/valid/TargetMutation8` illustrates this refinement.
                val eVars = terminalVarsOfExprDealiased(e, env)
                val bVars = varsOfExprDealiased(b, env)
                val commonMutable = (eVars & bVars).filter(v => isMutableType(v.tpe))
                if (commonMutable.isEmpty) {
                  // The above condition is similar to the one in EffectsChecker#check#traverser#traverse#Let, with the
                  // difference that we also account for rewrites (which may introduce other variables, as in i1099.scala).
                  val newBody = transform(b, env withBinding vd)

                  // for all effects of `b` whose receiver is `vd`
                  val copyEffects = effects(b).filter(_.receiver == vd.toVariable).flatMap { eff =>
                    // we apply the effect on the bound expression (after transformation)
                    eff.on(newExpr).map { case (eff2, cond2) => makeAssignment(l.getPos, eff.receiver, eff.path.path, eff2.toTarget(cond2)) }
                  }
                  val resVd = ValDef.fresh("res", b.getType).copiedFrom(b)

                  // What we would like is the following:
                  //   var vd = newExpr
                  //   val resVd = newBody
                  //   copyEffects // must happen after newBody and newExpr
                  //   resVd
                  // However, newBody may contain an `Ensuring` clause which would get "lost" in the newBody:
                  //   var vd = newExpr
                  //   val resVd = {
                  //      newBody'
                  //   }.ensuring(...) // oh no :(
                  //   copyEffects
                  //   resVd
                  // What we would like is something as follows:
                  //   var vd = newExpr
                  //   {
                  //      newBodyBlocks // e.g. assignments etc.
                  //      val resVd = newBodyLastExpr
                  //      copyEffect
                  //      resVd
                  //    }.ensuring(...)
                  // To achieve this, we "drill" a hole in newBody using the normalizer object,
                  // insert copyEffect and plug it with resVd. This should get us something like the above.
                  val (newBodyCtx, newBodyLastExpr) = normalizer.drill(newBody)
                  val (copyEffectCtx, copyEffectLastExpr) = normalizer.normalizeBlock(Block(copyEffects.toSeq, resVd.toVariable).copiedFrom(l))(using normalizer.BlockNorm.Standard)
                  assert(copyEffectLastExpr == resVd.toVariable) // To be sure we are on the good track.
                  val combined =
                    newBodyCtx(let(resVd, newBodyLastExpr, copyEffectCtx(resVd.toVariable)))
                  LetVar(vd, newExpr, combined).copiedFrom(l)
                } else {
                  val msg =
                    s"""Unsupported `val` definition in AntiAliasing
                       |The following variables of mutable types are shared between the binding and the body:
                       |  ${commonMutable.toSeq.sortBy(_.id.name).map(v => s"${v.id}: ${v.tpe}").mkString(", ")}""".stripMargin
                  throw MalformedStainlessCode(l, msg)
                }
            }

          case l @ LetVar(vd, e, b) if isMutableType(vd.tpe) =>
            val newExpr = transform(e, env)
            val newBody = transform(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case up @ ArrayUpdate(arr, i, v) =>
            assertReferentiallyTransparent(i)
            val recI = transform(i, env)
            val recV = transform(v, env)
            val targets = getDirectTargetsDealiased(arr, ArrayAccessor(recI), env)
              .getOrElse(throw MalformedStainlessCode(up, "Unsupported form of array updated"))

            val updates = updatedTargetsAndAliases(targets, recV, env, up.getPos)
            Block(updates, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case up @ MutableMapUpdate(map, k, v) =>
            assertReferentiallyTransparent(k)
            val recK = transform(k, env)
            val recV = transform(v, env)
            val targets = getDirectTargetsDealiased(map, MutableMapAccessor(recK), env)
              .getOrElse(throw MalformedStainlessCode(up, "Unsupported form of map updated"))

            val updates = updatedTargetsAndAliases(targets, recV, env, up.getPos)
            Block(updates, UnitLiteral().copiedFrom(up)).copiedFrom(up)

          case as @ FieldAssignment(o, id, v) =>
            val accessor = typeToAccessor(o.getType, id)
            val targets = getDirectTargetsDealiased(o, accessor, env)
              .getOrElse(throw MalformedStainlessCode(as, "Unsupported form of field assignment"))

            val recV = transform(v, env)
            val updates = updatedTargetsAndAliases(targets, recV, env, as.getPos)
            Block(updates, UnitLiteral().copiedFrom(as)).copiedFrom(as)

          // we need to replace local fundef by the new updated fun defs.
          case l @ LetRec(fds, body) =>
            val nfds = fds.map(fd => updateFunction(Inner(fd), env withLocals fds).toLocal)
            LetRec(nfds, transform(body, env withLocals fds)).copiedFrom(l)

          case e @ Ensuring(body, l @ Lambda(params, post)) =>
            Ensuring(transform(body, env), Lambda(params, transform(post, env)).copiedFrom(l)).copiedFrom(e)

          case l @ Lambda(params, body) =>
            val ft @ FunctionType(_, _) = l.getType: @unchecked
            val ownEffects = functionTypeEffects(ft)
            val aliasedParams: Seq[ValDef] = params.zipWithIndex.flatMap {
              case (vd, i) if ownEffects.contains(i) => Some(vd)
              case _ => None
            }
            // Disallow capturing of variables of mutable type
            val captured = varsOfExprDealiased(body, env).filter(vd => isMutableType(vd.tpe)) -- aliasedParams.map(_.toVariable).toSet
            if (captured.nonEmpty) {
              context.reporter.fatalError(l.getPos, "Illegal capturing of variables with mutable type: " + captured.mkString(", "))
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

            if (!fi.tfd.flags.exists(_.name == "accessor"))
              checkAliasing(fi, args, env)

            val nfi = FunctionInvocation(
              id, tps, args.map(transform(_, env))
            ).copiedFrom(fi)

            mapApplication(fd.params, args, nfi, fi.tfd.instantiate(analysis.getReturnType(fd)), effects(fd), env)

          case alr @ ApplyLetRec(id, tparams, tpe, tps, args) =>
            val fd = Inner(env.locals(id))
            checkAliasing(alr, args, env)
            // Get all variables captured by this fd, and follow their target aliasing as well
            val vis: Set[Variable] = varsInScope(fd)
              .flatMap(v =>
                env.targets.get(v.toVal).toSet.flatMap(_.map(_.receiver).toSet) ++ Set(v))
            // Then, compute the (dealiased) targets for all arguments.
            // If we find out that a captured variable is also passed as an argument, we declare the program ill-formed
            // because the argument will alias the captured variable.
            // For argument whose target cannot be computed, we resort to computing the set of mutable FV
            // (and follow their aliases), which is less precise.
            args.flatMap { a =>
              getAllTargetsDealiased(a, env).map(_.map(_.receiver))
                .getOrElse(varsOfExprDealiased(a, env))
            }.find(vis.contains)
              .foreach(v => context.reporter.fatalError(alr.getPos, "Illegal passing of aliased local variable: " + v))

            val nfi = ApplyLetRec(
              id, tparams,
              FunctionType(fd.params.map(_.getType), analysis.getReturnType(fd)).copiedFrom(tpe), tps,
              args.map(transform(_, env))
            ).copiedFrom(alr)

            val resultType = typeOps.instantiateType(analysis.getReturnType(fd), (tparams zip tps).toMap)
            mapApplication(fd.params, args, nfi, resultType, effects(fd), env)

          case app @ Application(callee, args) =>
            checkAliasing(app, args, env)

            val ft @ FunctionType(from, to) = callee.getType: @unchecked
            val ftEffects = functionTypeEffects(ft)
            if (ftEffects.nonEmpty) {
              val nfi = Application(
                transform(callee, env),
                args.map(transform(_, env))
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

          case cc @ ClassConstructor(_, args) =>
            checkAliasing(cc, args, env)
            super.transform(cc, env)

          case adt @ ADT(_, _, args) =>
            checkAliasing(adt, args, env)
            super.transform(adt, env)

          case tpl @ Tuple(exprs) =>
            checkAliasing(tpl, exprs, env)
            super.transform(tpl, env)

          case fa @ FiniteArray(elems, _) =>
            checkAliasing(fa, elems, env)
            super.transform(fa, env)

          case au @ ArrayUpdated(arr, i, v) =>
            assertReferentiallyTransparent(i)
            checkAliasing(au, Seq(arr, i, v), env)
            super.transform(au, env)

          case mu @ MapUpdated(map, k, v) =>
            assertReferentiallyTransparent(k)
            checkAliasing(mu, Seq(map, k, v), env)
            super.transform(mu, env)

          case Operator(es, recons) => recons(es.map(transform(_, env)))
        }).copiedFrom(e)

        def varsOfExprDealiased(expr: Expr, env: Env): Set[Variable] = {
          exprOps.variablesOf(expr).flatMap { v =>
            env.targets.get(v.toVal) match {
              case Some(targets) => targets.map(_.receiver)
              case None => Set(v)
            }
          }
        }

        def terminalVarsOfExprDealiased(expr: Expr, env: Env): Set[Variable] = {
          // Like `varsOfExprDealiased` but takes into account local binding in `vars`
          def varsOfExprDealiasedWithLocalBdgs(e: Expr, vars: Map[Variable, Set[Variable]]): Set[Variable] = {
            for {
              v <- exprOps.variablesOf(e)
              v1 <- vars.getOrElse(v, Set(v))
              v2 <- env.targets.get(v1.toVal).map(_.map(_.receiver)).getOrElse(Set(v1))
            } yield v2
          }
          // Note: we do not have to worry about reassignment (via FieldAssignment, ArrayUpdate, etc.)
          // because these must be fresh expressions and therefore cannot add further aliasing.
          def go(e: Expr, vars: Map[Variable, Set[Variable]]): Set[Variable] = e match {
            case Let(vd, df, body) =>
              val dfTargets = getAllTargetsDealiased(df, env)
              val dfVars = dfTargets match {
                case Some(dfTargets) =>
                  dfTargets.flatMap(t => vars.getOrElse(t.receiver, Set(t.receiver)))
                case None => varsOfExprDealiasedWithLocalBdgs(df, vars)
              }
              go(body, vars + (vd.toVariable -> dfVars))
            case LetVar(vd, _, body) =>
              assert(!isMutableType(vd.tpe))
              // No special handling is needed since `vd` is immutable
              go(body, vars)
            case Block(_, last) => go(last, vars)
            case LetRec(_, body) => go(body, vars)
            case Ensuring(body, _) => go(body, vars)
            case Assert(_, _, body) => go(body, vars)
            case Assume(_, body) => go(body, vars)
            case Decreases(_, body) => go(body, vars)
            case Require(_, body) => go(body, vars)
            case IfExpr(_, thn, elze) => go(thn, vars) ++ go(elze, vars)
            case MatchExpr(_, cases) => cases.flatMap(mc => go(mc.rhs, vars)).toSet
            case _ => varsOfExprDealiasedWithLocalBdgs(e, vars)
          }
          go(expr, Map.empty)
        }

        def assertReferentiallyTransparent(expr: Expr): Unit = {
          assert(isReferentiallyTransparent(expr), s"${expr.asString} is not referentially transparent")
        }
      }

      val transformer = new TransformerImpl(self.s, self.t)
      val normBody = normalizer.normalize(body)(using normalizer.BlockNorm.Standard)
      transformer.transform(normBody, env)
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
          val adt @ ADTType(_, tps) = receiver.getType: @unchecked
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
            throw FatalError(s"Could not find class for type ${receiver.getType}")
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
          val tt @ TupleType(_) = receiver.getType: @unchecked
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

        case Target(receiver, Some(BooleanLiteral(true)), path) =>
          rec(receiver, path.toSeq)

        case Target(receiver, Some(condition), path) if effects(condition).nonEmpty =>
          throw MalformedStainlessCode(condition, s"Effects are not allowed in condition of effects: ${condition.asString}")

        case Target(receiver, Some(condition), path) =>
          val recRecv = rec(receiver, path.toSeq)
          Annotated(
            AsInstanceOf(
              IfExpr(
                condition.setPos(newValue),
                Annotated(recRecv, Seq(DropVCs)).copiedFrom(recRecv),
                receiver
              ).copiedFrom(newValue),
              receiver.getType
            ).copiedFrom(newValue),
            Seq(DropVCs)
          ).copiedFrom(newValue)
      }
    }

    // Tries to simplify Or(es), leveraging the logical structure introduced by ITE expressions.
    // For instance, if es is of the form:
    //    Seq(cond1, !cond1 && cond2, !cond1 && !cond2, !cond1 && !cond2 && cond3)
    //    (corresponding to if (cond1) else if (cond2) else if (cond3))
    // Then, an equivalent Or(es) is:
    //    cond1 || cond2 || cond3
    // If `es` is empty, False is returned
    def simplifyOr(es: Seq[Expr]): Expr = {
      enum Lit {
        case Pos(e: Expr)
        case Neg(e: Expr)
        def inverted: Lit = this match {
          case Pos(e) => Neg(e)
          case Neg(e) => Pos(e)
        }
        def unwrap: Expr = this match {
          case Pos(e) => e
          case Neg(e) => Not(e).copiedFrom(e)
        }
      }
      import Lit._
      // Conjunction of "literals"
      case class Conj(lits: Set[Lit]) {
        require(lits.nonEmpty)
      }

      // Naive and inefficient loop performing some form of resolution,
      // using the fact that b1 || (!b1 && b2) === b1 || b2.
      // `res` is to be interpreted as a DNF, while `lits` contains
      // candidate literals for the resolution.
      def loop(lits: Set[Lit], res: Set[Conj]): Set[Conj] = {
        if (lits.isEmpty) res
        else {
          val currInv = lits.head.inverted
          res.find(_.lits.contains(currInv)) match {
            case Some(conj) =>
              val newConj = conj.lits.filter(_ != currInv)
              // If newConj is empty, we have found a literal b and its negated form !b; the entire DNF is true
              if (newConj.isEmpty) Set(Conj(Set(Pos(BooleanLiteral(true)))))
              else {
                // Add the resulting conjunction to the set of literal if it became a literal
                val newLits = if (newConj.size == 1) lits + newConj.head else lits
                loop(newLits, (res - conj) + Conj(newConj))
              }
            case None =>
              // No conjunction contains the inverted literal, we drop it and continue
              loop(lits.tail, res)
          }
        }
      }

      def wrap(e: Expr): Lit = e match {
        case Not(e) => wrap(e).inverted // Recursive call to ensure things such as Not(Not(e)) get mapped to Pos(e)
        case e => Pos(e)
      }

      def unwrapConj(conj: Conj): Expr = {
        val (pos, neg) = conj.lits.partitionMap {
          case Pos(e) => Left(e)
          case Neg(e) => Right(e)
        }
        if (pos.intersect(neg).nonEmpty) BooleanLiteral(false)
        else andJoin(pos.toSeq ++ neg.toSeq.map(simpleNot))
      }

      val (lits, conj) = es.foldLeft((Set.empty[Lit], Set.empty[Conj])) {
        case ((accLits, accConjs), And(conj)) =>
          (accLits, accConjs + Conj(conj.map(wrap).toSet))
        case ((accLits, accConjs), e) =>
          // "literals" are also candidate for simplification
          (accLits + wrap(e), accConjs + Conj(Set(wrap(e))))
      }

      val simp = loop(lits, conj)
      orJoin(simp.map(unwrapConj).toSeq)
    }
    // This function essentially wraps an e into a Not(e), except if we can do very simple simplification.
    // The use case is to keep the Not(..) structure around for simplifyOr to be more effective.
    def simpleNot(e: Expr): Expr = e match {
      case BooleanLiteral(b) => BooleanLiteral(!b).copiedFrom(e)
      case Not(e) => e
      case e => Not(e).copiedFrom(e)
    }

    def appearsInAssignment(vd: Variable, e: Expr): Boolean = {
      exprOps.exists {
        case Assignment(`vd`, _) => true
        case _ => false
      }(e)
    }

    // Pre-transformation phase to ease the burden of makeSideEffectsExplicit.
    // In particular, we:
    //   -Hoist blocks out of expressions.
    //    For instance, we transform:
    //       f({stmts1; last1}, {stmts2; last2})
    //    into:
    //       stmts1; val last1' = last1; stmts2; val last2' = last2
    //       f(last1', last2')
    //
    //   -Hoist let-binding appearing within let bindings
    //
    //   -Introduce extra bindings for arrays and map indices whenever
    //   they are not referentially transparent.
    //   For instance, assuming `i` is a `var`, we transform:
    //       arr(i); i += 1; arr(i)
    //   into:
    //       val ix1 = i; arr(ix1); i += 1; val ix2 = i; arr(ix2)
    //   The main reason for this binding is when manipulating targets.
    //   Intuitively, the target arr(i) before the increment is different
    //   from the one after the increment, however, we cannot distinguish them
    //   syntactically.
    //   By introducing `ix1` and `ix2`, we can refer to targets `arr(ix1)` and `arr(ix2)`
    //   unambiguously, anywhere in the rest of the function.
    //
    //   -Introduce extra bindings for expression appearing in "target position"
    //   (field assignment, array update, etc.).
    //   For instance, we transform:
    //       (if (cond) box1 else box2).value = 1234
    //   into:
    //       val targetBound = if (cond) box1 else box2
    //       targetBound.value = 1234
    //
    object normalizer {
      // Dictates the normalization to be done on blocks.
      // Standard is keeping the block while IntoLet sequence the statements into lets.
      // Let-transformation of blocks is only used for normalizing the predicate of `require` and `decreases`.
      // These must be chained within lets and not blocks.
      enum BlockNorm {
        case Standard
        case IntoLet
      }

      def normalize(e: Expr)(using BlockNorm): Expr = {
        val (ctx, norm) = doNormalize(e)
        ctx(norm)
      }

      def drill(toDrill: Expr): (Expr => Expr, Expr) = {
        def helper(subpartToDrill: Expr)(recons: Expr => Expr) = {
          val (subCtx, subExpr) = drill(subpartToDrill)
          val ctx = (e: Expr) => recons(subCtx(e)).copiedFrom(toDrill)
          (ctx, subExpr)
        }

        toDrill match {
          case Block(stmts, last) => helper(last)(Block(stmts, _))
          case Let(vd, df, body) => helper(body)(Let(vd, df, _))
          case LetVar(vd, df, body) => helper(body)(LetVar(vd, df, _))
          case LetRec(fds, body) => helper(body)(LetRec(fds, _))
          case Lambda(vds, body) => helper(body)(Lambda(vds, _))
          case Choose(vd, body) => helper(body)(Choose(vd, _))
          case Forall(vds, body) => helper(body)(Forall(vds, _))
          case Ensuring(body, l) => helper(body)(Ensuring(_, l))
          case Assert(pred, err, body) => helper(body)(Assert(pred, err, _))
          case Assume(pred, body) => helper(body)(Assume(pred, _))
          case Decreases(pred, body) => helper(body)(Decreases(pred, _))
          case Require(pred, body) => helper(body)(Require(pred, _))
          case _ => (identity, toDrill)
        }
      }

      // The actual work, we perform normalization using the unreasonably effective "hole technique".
      // The normalization of an expression e, [|e|], yields a context with a hole C, and the normalized expression e'.
      // This context intuitively represents all extra bindings needed for e' to be well-formed.
      // If we plug C with e' itself, we obtain a self-contained, normalized expression.
      //
      // The rules for let bindings and blocks are of interest (the other cases are similar to each other
      // are obtained by combining the recursive results together):
      //   -For [|let vd = e in body|], if [|e|] ~> Ce, e'  and  [|body|] ~> Cb, body',
      //    then [|let vd = e in body|] ~> Ce[let vd = e' in Cb[ [] ] ], body'
      //
      //   -For [[{stmt1; stmt2; ...; last}|], if [|stmti|] ~> Ci, stmti' and [|last|] ~> Cl, last'
      //    then [[{stmt1; stmt2; ...; last}|] ~> {C1[stmt1']; C2[stmt2']; ..., []}, last'
      //
      def doNormalize(e: Expr)(using BlockNorm): (Expr => Expr, Expr) = e match {
        case cs @ ClassSelector(_, _) if selectionNeedsNorm(cs) =>
          normalizeForTarget(cs)

        case ts @ TupleSelect(_, _) if selectionNeedsNorm(ts) =>
          normalizeForTarget(ts)

        case adt @ ADTSelector(_, _) if selectionNeedsNorm(adt) =>
          normalizeForTarget(adt)

        case as @ ArraySelect(_, _) =>
          normalizeForTarget(as)

        case ma @ MapApply(_, _) =>
          normalizeForTarget(ma)

        case ma @ MutableMapApply(_, _) =>
          normalizeForTarget(ma)

        case asgn @ Assignment(vr, value) =>
          val (ctxValue, normValue) = doNormalize(value)
          (ctxValue, Assignment(vr, normValue).copiedFrom(asgn))

        case fs @ FieldAssignment(o, id, v) =>
          val (ctxO, normO) = normalizeForTarget(o)
          val (ctxV, normV) = doNormalize(v)
          (ctxO compose ctxV, FieldAssignment(normO, id, normV).copiedFrom(fs))

        case up @ ArrayUpdate(arr, i, v) =>
          val (ctxArr, normArr) = normalizeForTarget(arr)
          val (ctxI, normI) = normalizeSelector(i)
          val (ctxV, normV) = doNormalize(v)
          (ctxArr compose ctxI compose ctxV, ArrayUpdate(normArr, normI, normV).copiedFrom(up))

        case up @ ArrayUpdated(arr, i, v) =>
          val (ctxArr, normArr) = normalizeForTarget(arr)
          val (ctxI, normI) = normalizeSelector(i)
          val (ctxV, normV) = doNormalize(v)
          (ctxArr compose ctxI compose ctxV, ArrayUpdated(normArr, normI, normV).copiedFrom(up))

        case up @ MutableMapUpdate(map, k, v) =>
          val (ctxMap, normMap) = normalizeForTarget(map)
          val (ctxK, normK) = normalizeSelector(k)
          val (ctxV, normV) = doNormalize(v)
          (ctxMap compose ctxK compose ctxV, MutableMapUpdate(normMap, normK, normV).copiedFrom(up))

        case up @ MutableMapUpdated(map, k, v) =>
          val (ctxMap, normMap) = normalizeForTarget(map)
          val (ctxK, normK) = normalizeSelector(k)
          val (ctxV, normV) = doNormalize(v)
          (ctxMap compose ctxK compose ctxV, MutableMapUpdated(normMap, normK, normV).copiedFrom(up))

        case swp @ Swap(arr1, i1, arr2, i2) =>
          val (ctxArr1, normArr1) = normalizeForTarget(arr1)
          val (ctxI1, normI1) = normalizeSelector(i1)
          val (ctxArr2, normArr2) = normalizeForTarget(arr2)
          val (ctxI2, normI2) = normalizeSelector(i2)
          (ctxArr1 compose ctxI1 compose ctxArr2 compose ctxI2, Swap(normArr1, normI1, normArr2, normI2).copiedFrom(swp))

        case swp @ CellSwap(cell1, cell2) =>
          val (ctxCell1, normCell1) = normalizeForTarget(cell1)
          val (ctxCell2, normCell2) = normalizeForTarget(cell2)
          (ctxCell1 compose ctxCell2, CellSwap(normCell1, normCell2).copiedFrom(swp))

        case call: (Application | FunctionInvocation | ApplyLetRec) =>
          normalizeCall(call)

        case ite @ IfExpr(cond, thn, els) =>
          val (ctxCond, normCond) = normalizeForTarget(cond)
          // We may not hoist bindings out of the branches.
          val normThn = normalize(thn)
          val normEls = normalize(els)
          (ctxCond, IfExpr(normCond, normThn, normEls).copiedFrom(ite))

        case mtch @ MatchExpr(scrut, cases) =>
          val (ctxScrut, normScrut) = normalizeForTarget(scrut)
          val normCases = cases.map {
            case mc@MatchCase(pattern, guard, rhs) =>
              // We transform:
              //   scrut match {
              //     case C(a1, ..., an) if guard => rhs
              //   }
              // into:
              //   scrut' match {
              //     case C(a1, ..., an) if guard'' => rhs''
              //   }
              // where rhs'' is defined as (and similar for guard''):
              //   var a1' = scrut'.asInstanceOf[C].a1
              //   ...
              //   var an' = scrut'.asInstanceOf[C].an
              //   rhs'[a1 -> a1', ..., an -> an']
              // where scrut' and rhs' denote normalized expressions.
              //
              // The motivation behind this normalization is to facilitate the handling of pattern matching
              // for the makeSideEffectsExplicit transformation, especially towards targets computation.
              // Indeed, the target of ai' is just scrut'.asInstanceOf[C].ai
              // (on the other hand, the target of the original `ai` is `ai` itself, which doesn't tie it to the scrutinee!
              // As such, we would need to introduce extra machinery in makeSideEffectsExplicit to ensure correctness).
              //
              // Since this transformation is only performed for target computation, we can avoid introducing
              // bindings for variables of immutable types, as these are not affected by mutation.
              val patternBindings: Map[ValDef, Expr] = mapForPattern(normScrut, pattern)
              val mutVds = patternBindings.keySet.filter(vd => isMutableType(vd.tpe))
              val (normGuard, normRhs) = {
                if (mutVds.nonEmpty) {
                  def bindAndNormalize(e: Expr): Expr = {
                    val freshVds = mutVds.map(origVd => origVd -> origVd.freshen)
                    val substMap = freshVds.map { case (origVd, freshVd) => origVd -> freshVd.toVariable }.toMap
                    val substed = replaceFromSymbols(substMap, e)
                    val norm = normalize(substed)
                    freshVds.foldRight(norm) {
                      case ((origVd, freshVd), acc) =>
                        let(freshVd, patternBindings(origVd), acc).copiedFrom(e)
                    }
                  }
                  val normGuard = guard.map(bindAndNormalize)
                  val normRhs = bindAndNormalize(rhs)
                  (normGuard, normRhs)
                } else {
                  (guard.map(normalize), normalize(rhs))
                }
              }
              MatchCase(pattern, normGuard, normRhs).copiedFrom(mc)
          }
          (ctxScrut, MatchExpr(normScrut, normCases).copiedFrom(mtch))

        case b @ Block(_, _) =>
          normalizeBlock(b)

        case let @ Let(_, _, _) =>
          normalizeLet(let)

        case let @ LetVar(_, _, _) =>
          normalizeLet(let)

        case l @ Lambda(params, body) =>
          (identity, Lambda(params, normalize(body)).copiedFrom(l))

        case l @ LetRec(fds, body) =>
          val normFds = fds.map(fd => fd.copy(fullBody = normalize(fd.fullBody)))
          (identity, LetRec(normFds, normalize(body)).copiedFrom(l))

        case whle @ While(cond, body, pred, pred2, flags) =>
          (identity, While(normalize(cond), normalize(body), pred.map(normalize), pred2.map(normalize), flags).copiedFrom(whle))

        case asrt @ Assert(pred, err, body) =>
          val (ctxPred, normPred) = doNormalize(pred)
          (ctxPred, Assert(normPred, err, normalize(body)).copiedFrom(asrt))

        case asm @ Assume(pred, body) =>
          val (ctxPred, normPred) = doNormalize(pred)
          (ctxPred, Assume(normPred, normalize(body)).copiedFrom(asm))

        case dec @ Decreases(pred, body) =>
          val (ctxPred, normPred) = doNormalize(pred)(using BlockNorm.IntoLet)
          (ctxPred, Decreases(normPred, normalize(body)).copiedFrom(dec))

        case req @ Require(pred, body) =>
          val (ctxPred, normPred) = doNormalize(pred)(using BlockNorm.IntoLet)
          (ctxPred, Require(normPred, normalize(body)).copiedFrom(req))

        case ens @ Ensuring(body, l @ Lambda(vds, lamBody)) =>
          // Do not hoist expression out of the body as we want to keep the enclosing Ensuring(...) structure.
          (identity, Ensuring(normalize(body), Lambda(vds, normalize(lamBody)).copiedFrom(l)).copiedFrom(ens))

        case ann @ Annotated(e, flags) =>
          (identity, Annotated(normalize(e), flags).copiedFrom(ann))

        case fa @ Forall(vds, pred) =>
          (identity, Forall(vds, normalize(pred)).copiedFrom(fa))

        case ch @ Choose(vds, pred) =>
          (identity, Choose(vds, normalize(pred)).copiedFrom(ch))

        case _: (And | Or | Implies | Not) =>
          // Similar to if-then-else, we may not hoist expression out of these expressions (in particular && || and ==> are short-circuiting)
          val Operator(args, recons) = e: @unchecked
          (identity, recons(args.map(normalize)).copiedFrom(e))

        case Operator(args, recons) =>
          val (ctxArgs, normArgs) = normalizeArgs(args)
          (ctxArgs, recons(normArgs).copiedFrom(e))
      }

      // For indices and keys
      def normalizeSelector(sel: Expr)(using BlockNorm): (Expr => Expr, Expr) = {
        assert(!isMutableType(sel.getType))
        if (!isReferentiallyTransparent(sel)) {
          val valIx = Variable(FreshIdentifier("ix"), sel.getType, Seq.empty).copiedFrom(sel)
          val (ctxIx, normIx) = doNormalize(Let(new ValDef(valIx), sel, valIx).copiedFrom(sel))
          assert(normIx == valIx)
          (ctxIx, normIx)
        } else {
          (identity, sel)
        }
      }

      def normalizeForTarget(targetExpr: Expr)(using BlockNorm): (Expr => Expr, Expr) = targetExpr match {
        case v @ Variable(_, _, flags) =>
          if (flags.contains(IsVar)) {
            val newVal = v.copy(id = FreshIdentifier(s"${v.id.name}Cpy"), flags = flags.filter(_ != IsVar)).copiedFrom(v)
            val ctx = (e: Expr) => Let(new ValDef(newVal).copiedFrom(v), v, e).copiedFrom(v)
            (ctx, newVal)
          } else {
            (identity, v)
          }
        case adt @ ADTSelector(recv, sel) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          (ctxRecv, ADTSelector(normRecv, sel).copiedFrom(adt))
        case tpl @ TupleSelect(recv, ix) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          (ctxRecv, TupleSelect(normRecv, ix).copiedFrom(tpl))
        case cs @ ClassSelector(recv, sel) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          (ctxRecv, ClassSelector(normRecv, sel).copiedFrom(cs))
        case as @ ArraySelect(recv, i) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          val (ctxI, normI) = normalizeSelector(i)
          (ctxRecv compose ctxI, ArraySelect(normRecv, normI).copiedFrom(as))
        case ma @ MapApply(recv, k) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          val (ctxK, normK) = normalizeSelector(k)
          (ctxRecv compose ctxK, MapApply(normRecv, normK).copiedFrom(ma))
        case ma @ MutableMapApply(recv, k) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          val (ctxK, normK) = normalizeSelector(k)
          (ctxRecv compose ctxK, MutableMapApply(normRecv, normK).copiedFrom(ma))
        case ann @ Annotated(recv, anns) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          (ctxRecv, Annotated(normRecv, anns).copiedFrom(ann))
        case aio @ AsInstanceOf(recv, tpe) =>
          val (ctxRecv, normRecv) = normalizeForTarget(recv)
          (ctxRecv, AsInstanceOf(normRecv, tpe).copiedFrom(aio))
        case _ =>
          val (ctxExpr, normExpr) = doNormalize(targetExpr)
          val targetVal = Variable(FreshIdentifier("targetBound"), targetExpr.getType, Seq.empty).copiedFrom(targetExpr)
          val ctx = (e: Expr) => ctxExpr(Let(new ValDef(targetVal).copiedFrom(targetExpr), normExpr, e).copiedFrom(targetExpr))
          (ctx, targetVal)
      }

      def normalizeArgs(args: Seq[Expr])(using BlockNorm): (Expr => Expr, Seq[Expr]) = {
        def occurInAssignment(vs: Set[Variable], expr: Expr): Boolean = expr match {
          case Assignment(v, e) => vs.contains(v) || occurInAssignment(vs, e)
          case FieldAssignment(recv, _, e) => (exprOps.variablesOf(recv) & vs).nonEmpty || occurInAssignment(vs, e)
          case ArrayUpdate(arr, i, e) => (exprOps.variablesOf(arr) & vs).nonEmpty || occurInAssignment(vs, i) || occurInAssignment(vs, e)
          case MutableMapUpdate(map, k, e) => (exprOps.variablesOf(map) & vs).nonEmpty || occurInAssignment(vs, k) || occurInAssignment(vs, e)
          case Operator(es, _) => es.exists(occurInAssignment(vs, _))
        }

        val (ctxs: Seq[Expr => Expr], normArgs) = args.indices.map { i =>
          val arg = args(i)
          val restArgs = args.drop(i + 1)
          val (ctxArg, normArg) = doNormalize(arg)
          // Since the arguments following the current arg may modify variables referred by the current arg,
          // we need to introduce bindings to enforce sequencing.
          // For instance, in:
          //    f(i, {i += 1; j})
          // we need to create a copy of `i`:
          //    val argBound = i
          //    i += 1
          //    f(argBound, j) // Block hoisted by the recursive process
          //
          // However, most expressions do not modify their arguments: as such, we can avoid introducing extra bindings in these cases.
          val varsOfNormArg = exprOps.variablesOf(normArg)
          val needsBinding = restArgs.exists(occurInAssignment(varsOfNormArg, _))
          if (needsBinding) {
            val argBound = Variable(FreshIdentifier(s"argBound_$i"), arg.getType, Seq.empty).copiedFrom(arg)
            val ctx = (e: Expr) => ctxArg(Let(new ValDef(argBound).copiedFrom(arg), normArg, e).copiedFrom(argBound))
            (ctx, argBound)
          } else {
            (ctxArg, normArg)
          }
        }.unzip

        (ctxs.foldRight(identity[Expr])(_ compose _), normArgs)
      }

      def unlet(let: Let | LetVar): (ValDef, Expr, Expr) = let match {
        case Let(vd, value, body) => (vd, value, body)
        case LetVar(vd, value, body) => (vd, value, body)
      }

      def let(vd: ValDef, value: Expr, body: Expr): Let | LetVar = {
        if (vd.flags.contains(IsVar)) LetVar(vd, value, body).copiedFrom(value)
        else Let(vd, value, body).copiedFrom(value)
      }

      def normalizeBlock(block: Block)(using bn: BlockNorm): (Expr => Expr, Expr) = {
        val normExprs: Seq[(Expr => Expr, Expr)] = (block.exprs :+ block.last).map(doNormalize)

        val (ctxLast, normLast) = normExprs.last
        val ctxBlock = (e: Expr) => {
          if (normExprs.size == 1) ctxLast(e).copiedFrom(block) // Note: normExprs == Seq((ctxLast, normLast))
          else bn match {
            case BlockNorm.Standard =>
              val init = normExprs.init.map((ctx, e) => ctx(e))
              Block(init, ctxLast(e)).copiedFrom(block)
            case BlockNorm.IntoLet =>
              normExprs.init.foldRight(ctxLast(e)) {
                case ((ctx, e), acc) =>
                  val vd = ValDef.fresh("tmp", e.getType).copiedFrom(e)
                  let(vd, ctx(e), acc)
              }.copiedFrom(block)
          }
        }
        (ctxBlock, normLast)
      }

      def normalizeLet(lt: Let | LetVar)(using BlockNorm): (Expr => Expr, Expr) = {
        val (vd, value, body) = unlet(lt)
        val (ctxValue, normValue) = doNormalize(value)
        val (ctxBody, normBody) = doNormalize(body)
        val ctxLet = (e: Expr) => ctxValue(let(vd, normValue, ctxBody(e)).copiedFrom(lt))
        (ctxLet, normBody)
      }

      def normalizeCall(call: Application | FunctionInvocation | ApplyLetRec)(using BlockNorm): (Expr => Expr, Expr) = {
        val (ft, args, ctxCallee: (Expr => Expr), recons: (Seq[Expr] => Expr)) = call match {
          case app @ Application(callee, args) =>
            val ft @ FunctionType(_, _) = callee.getType: @unchecked
            val (ctxCallee, normCallee) = doNormalize(callee)
            val recons: Seq[Expr] => Expr = Application(normCallee, _).copiedFrom(app)
            (ft, args, ctxCallee, recons)
          case fi @ FunctionInvocation(id, tps, args) =>
            val recons: Seq[Expr] => Expr = FunctionInvocation(id, tps, _).copiedFrom(fi)
            (fi.tfd.functionType, args, identity[Expr], recons)
          case alr @ ApplyLetRec(id, tparams, ft, tps, args) =>
            val recons: Seq[Expr] => Expr = ApplyLetRec(id, tparams, ft, tps, _).copiedFrom(alr)
            (ft, args, identity[Expr], recons)
        }
        val (ctxArgs, normArgs) = normalizeArgs(args)
        val normCall = recons(normArgs)
        (ctxCallee compose ctxArgs, normCall)
      }

      // Whether we need to normalize the receiver object and the corresponding selection.
      // If we treat immutable types, we do not need to introduce extra bindings,
      // as the set of targets for immutable types is empty.
      def selectionNeedsNorm(e: ClassSelector | TupleSelect | ADTSelector): Boolean = e match {
        case ClassSelector(recv, sel) =>
          val ct @ ClassType(_, _) = recv.getType: @unchecked
          isMutableType(e.getType) || ct.getField(sel).get.flags.contains(IsVar)
        case TupleSelect(_, _) =>
          isMutableType(e.getType)
        case ADTSelector(_, _) =>
          isMutableType(e.getType)
      }
    }

    val result = transformer.transform(updateFunction(Outer(fd), Environment.empty).toFun)
    val unchanged = result.id == fd.id && result.tparams == fd.tparams && result.params == fd.params &&
      result.returnType == fd.returnType && result.flags == fd.flags && result.fullBody == fd.fullBody
    val summary = if (unchanged) FunctionSummary.Untransformed(fd.id) else FunctionSummary.Transformed(fd.id)
    (Some(result), summary)
  }

  override protected type SortSummary = Unit
  override protected def extractSort(analysis: SymbolsAnalysis, sort: ADTSort): (ADTSort, Unit) =
    (analysis.transformer.transform(sort), ())

  override protected type ClassSummary = Unit
  override protected def extractClass(analysis: SymbolsAnalysis, cd: ClassDef): (ClassDef, Unit) =
    (analysis.transformer.transform(cd), ())

  override protected def combineSummaries(allSummaries: AllSummaries): ExtractionSummary = {
    val affectedFns = allSummaries.fnsSummary.collect { case FunctionSummary.Transformed(fid) => fid }
    ExtractionSummary.Leaf(AntiAliasing)(AntiAliasing.SummaryData(affectedFns.toSet))
  }
}

object AntiAliasing extends ExtractionPipelineCreator {
  case class SummaryData(affectedFns: Set[Identifier] = Set.empty) {
    def ++(other: SummaryData): SummaryData = SummaryData(affectedFns ++ other.affectedFns)
    def hasRun: Boolean = affectedFns.nonEmpty
  }

  override val name: String = "AntiAliasing"

  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends AntiAliasing(s)(t)
    new Impl(trees, trees)
  }
}
