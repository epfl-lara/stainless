/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

sealed abstract class CheckResult
object CheckResult {
  case object Ok extends CheckResult
  case object Skip extends CheckResult
  case class Error(err: ImperativeEliminationException) extends CheckResult
}

trait EffectsChecker { self: EffectsAnalyzer =>
  import s._
  import exprOps._

  protected def checkEffects(fd: FunDef)(analysis: EffectsAnalysis): CheckResult = {
    import analysis._
    import symbols.isMutableType

    def isMutableSynthetic(id: Identifier): Boolean = {
      val fd = symbols.getFunction(id)
      fd.flags.contains(Synthetic) &&
      !isAccessor(Outer(fd)) &&
      fd.params.exists(vd => isMutableType(vd.tpe)) &&
      !exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.forall(isExpressionFresh)
    }

    def isAccessor(fd: FunAbstraction): Boolean = {
      fd.flags.exists(_.name == "accessor")
    }

    // We can safely get rid of the function as we are assured
    // by the registry that, if the erroneous function being considered is
    // still present in the symbols, then it must be used somewhere else,
    // which is where we will want to report the error from, and abort the pipeline.
    if (isMutableSynthetic(fd.id)) return CheckResult.Skip

    def check(fd: FunAbstraction): Unit = {
      checkMutableField(fd)
      checkEffectsLocations(fd)
      checkPurity(fd)

      // Recursive functions must return fresh results so that no aliasing is possible
      if ((symbols.isRecursive(fd.id) || fd.isInstanceOf[Inner]) &&
          !exprOps.withoutSpecs(fd.fullBody).forall(isExpressionFresh))
        throw ImperativeEliminationException(fd, "Illegal recursive functions returning non-fresh result")

      object traverser extends SelfTreeTraverser {
        override def traverse(tpe: Type): Unit = tpe match {
          case at @ ADTType(id, tps) =>
            (at.getSort.definition.tparams zip tps).foreach { case (tdef, instanceType) =>
              if (isMutableType(instanceType) && !(tdef.flags contains IsMutable))
                throw ImperativeEliminationException(tpe,
                  s"Cannot instantiate a non-mutable ADT type parameter ${tdef.asString} with a mutable type ${instanceType.asString}")
            }

            super.traverse(at)

          case ct @ ClassType(id, tps) =>
            (ct.tcd.cd.tparams zip tps).foreach { case (tdef, instanceType) =>
              if (isMutableType(instanceType) && !(tdef.flags contains IsMutable))
                throw ImperativeEliminationException(tpe,
                  s"Cannot instantiate a non-mutable class type parameter ${tdef.asString} with a mutable type ${instanceType.asString}")
            }

            super.traverse(ct)

          case _ => super.traverse(tpe)
        }

        override def traverse(e: Expr): Unit = e match {
          case l @ Let(vd, e, b) =>
            if (
              (variablesOf(e) & variablesOf(b)).exists(v => isMutableType(v.tpe)) &&
              !isExpressionFresh(e) &&
              isMutableType(vd.tpe)
            ) try {
              // Check if a precise effect can be computed
              getTargets(e)
            } catch {
              case _: MalformedStainlessCode =>
                throw ImperativeEliminationException(e, "Illegal aliasing: " + e.asString)
            }

            super.traverse(l)

          case l @ LetVar(vd, e, b) =>
            if (!isExpressionFresh(e) && isMutableType(vd.tpe))
              throw ImperativeEliminationException(e, "Illegal aliasing: " + e.asString)

            super.traverse(l)

          case au @ ArrayUpdate(a, i, e) =>
            if (isMutableType(e.getType) && !isExpressionFresh(e))
              throw ImperativeEliminationException(e, "Illegal aliasing: " + e.asString)

            super.traverse(au)

          case mu @ MapUpdated(m, k, e) =>
            if (isMutableType(e.getType) && !isExpressionFresh(e))
              throw ImperativeEliminationException(e, "Illegal aliasing: " + e.asString)

            super.traverse(mu)

          case fa @ FieldAssignment(o, sel, e) =>
            if (isMutableType(fa.getField.get.getType) && !isExpressionFresh(e))
              throw ImperativeEliminationException(e, "Illegal aliasing: " + e.asString)

            super.traverse(fa)

          case l @ LetRec(fds, body) =>
            fds.foreach(fd => check(Inner(fd)))
            traverse(body)

          case l @ Lambda(args, body) =>
            if (isMutableType(body.getType) && !isExpressionFresh(body))
              throw ImperativeEliminationException(l, "Illegal aliasing in lambda body")
            if (effects(body).exists(e => !args.contains(e.receiver.toVal)))
              throw ImperativeEliminationException(l, "Illegal effects in lambda body")
            super.traverse(l)

          case fi: FunctionInvocation if isMutableSynthetic(fi.id) =>
            throw ImperativeEliminationException(fi, s"Cannot call '${fi.id.asString}' on a class with mutable fields")

          case fi @ FunctionInvocation(id, tps, args) =>
            val fd = symbols.getFunction(id)
            for ((tpe, tp) <- tps zip fd.tparams if (isMutableType(tpe) && !tp.flags.contains(IsMutable))) {
              throw ImperativeEliminationException(e,
                s"Cannot instantiate a non-mutable function type parameter ${tp.asString} in ${fi.asString} with the mutable type ${tpe.asString}")
            }

            super.traverse(fi)

          case adt @ ADT(id, tps, args) =>
            (adt.getConstructor.sort.definition.tparams zip tps).foreach { case (tdef, instanceType) =>
              if (isMutableType(instanceType) && !(tdef.flags contains IsMutable))
                throw ImperativeEliminationException(e,
                  s"Cannot instantiate a non-mutable ADT constructor type parameter ${tdef.asString} in ${adt.asString} with a mutable type ${instanceType.asString}")
            }

            super.traverse(adt)

          case MutableMapUpdated(m, k, v) =>
            m.getType match {
              case MutableMapType(_, to) if !isMutableType(to) => ()
              case _ =>
                throw ImperativeEliminationException(e,
                  s"Cannot use `updated` on a MutableMap whose range is a mutable type (${m.getType}).")
            }

          case MutableMapDuplicate(m) =>
            m.getType match {
              case MutableMapType(_, to) if !isMutableType(to) => ()
              case _ =>
                throw ImperativeEliminationException(e,
                  s"Cannot use `duplicate` on a MutableMap whose range is a mutable type (${m.getType}).")
            }

          case _ => super.traverse(e)
        }
      }

      traverser.traverse(fd.fullBody)
      for (param <- fd.params) traverser.traverse(param.tpe)
    }

    def checkMutableField(fd: FunAbstraction): Unit = {
      if (!fd.flags.exists { case IsField(_) => true case _ => false }) return ()

      if (isMutableType(fd.returnType))
        throw ImperativeEliminationException(fd, "A field cannot refer to a mutable object")

      if (effects(fd.fullBody).nonEmpty)
        throw ImperativeEliminationException(fd, s"A field must be pure, but ${fd.id.asString} has effects: ${effects(fd.fullBody).map(_.asString).mkString(", ")}")
    }

    def checkEffectsLocations(fd: FunAbstraction): Unit = exprOps.preTraversal {
      case Require(pre, _) =>
        val preEffects = effects(pre)
        if (preEffects.nonEmpty)
          throw ImperativeEliminationException(pre, "Precondition has effects on: " + preEffects.head.receiver.asString)

      case Ensuring(_, post @ Lambda(_, body)) =>
        val bodyEffects = effects(body)
        if (bodyEffects.nonEmpty)
          throw ImperativeEliminationException(post, "Postcondition has effects on: " + bodyEffects.head.receiver.asString)

        val oldEffects = effects(exprOps.postMap {
          case Old(e) => Some(e)
          case _ => None
        } (body))
        if (oldEffects.nonEmpty)
          throw ImperativeEliminationException(post, s"Postcondition tries to mutate ${Old(oldEffects.head.receiver).asString}")

      case Decreases(meas, _) =>
        val measEffects = effects(meas)
        if (measEffects.nonEmpty)
          throw ImperativeEliminationException(meas, "Decreases has effects on: " + measEffects.head.receiver.asString)

      case Assert(pred, _, _) =>
        val predEffects = effects(pred)
        if (predEffects.nonEmpty)
          throw ImperativeEliminationException(pred, "Assertion has effects on: " + predEffects.head.receiver.asString)

      case Forall(_, pred) =>
        val predEffects = effects(pred)
        if (predEffects.nonEmpty)
          throw ImperativeEliminationException(pred, "Quantifier has effects on: " + predEffects.head.receiver.asString)

      case wh @ While(_, _, Some(invariant), _) =>
        val invEffects = effects(invariant)
        if (invEffects.nonEmpty)
          throw ImperativeEliminationException(invariant, "Loop invariant has effects on: " + invEffects.head.receiver.asString)

      case m @ MatchExpr(_, cses) =>
        cses.foreach { cse =>
          cse.optGuard.foreach { guard =>
            val guardEffects = effects(guard)
            if (guardEffects.nonEmpty)
              throw ImperativeEliminationException(guard, "Pattern guard has effects on: " + guardEffects.head.receiver.asString)
          }

          patternOps.preTraversal {
            case up: UnapplyPattern =>
              val upEffects = effects(Outer(up.getFunction.fd))
              if (upEffects.nonEmpty)
                throw ImperativeEliminationException(up, "Pattern unapply has effects on: " + upEffects.head.receiver.asString)

            case _ => ()
          }(cse.pattern)
        }

      case Let(vd, v, rest) if vd.flags.contains(Lazy) =>
        val eff = effects(v)
        if (eff.nonEmpty)
          throw ImperativeEliminationException(v, "Stainless does not support effects in lazy val's on: " + eff.head.receiver.asString)

      case _ => ()
    }(fd.fullBody)

    def checkPurity(fd: FunAbstraction): Unit = {
      val effs = effects(fd.fullBody)

      if ((fd.flags contains IsPure) && !effs.isEmpty)
        throw ImperativeEliminationException(fd, s"Functions marked @pure cannot have side-effects")

      effs filter (_.receiver.flags.contains(IsPure)) foreach { eff =>
        throw ImperativeEliminationException(fd,
          s"Function `${fd.id.asString}` has effect on @pure parameter `${eff.receiver.asString}`")
      }
    }

    /* A fresh expression is an expression that is newly created
     * and does not share memory with existing values and variables.
     *
     * If the expression is made of existing immutable variables (Int or
     * immutable case classes), it is considered fresh as we consider all
     * non mutable objects to have a value-copy semantics.
     *
     * It turns out that an expression of non-mutable type is always fresh,
     * as it can not contains reference to a mutable object, by definition
     */
    def isExpressionFresh(expr: Expr): Boolean = {
      def rec(expr: Expr, bindings: Set[ValDef]): Boolean = !isMutableType(expr.getType) || (expr match {
        case v: Variable => bindings(v.toVal)
        case ADT(_, _, args) => args.forall(rec(_, bindings))

        case FiniteArray(elems, _) => elems.forall(rec(_, bindings))
        case LargeArray(elems, default, _, _) => elems.forall(p => rec(p._2, bindings)) && rec(default, bindings)

        // We assume `old(.)` is fresh here, although such cases will probably be
        // rejected later in `ImperativeCleanup`.
        case Old(_) => true

        case fi @ FunctionInvocation(id, _, _) if !symbols.isRecursive(id) =>
            BodyWithSpecs(symbols.simplifyLets(fi.inlined))
              .bodyOpt
              .forall(isExpressionFresh)

        // other function invocations always return a fresh expression, by hypothesis (global assumption)
        case (_: FunctionInvocation | _: ApplyLetRec | _: Application) => true

        //ArrayUpdated returns a mutable array, which by definition is a clone of the original
        case ArrayUpdated(IsTyped(_, ArrayType(base)), _, _) => !isMutableType(base)

        //MutableMapDuplicate returns a fresh duplicate by definition
        case MutableMapDuplicate(IsTyped(_, MutableMapType(from, to))) =>
          !isMutableType(from) && !isMutableType(to)

        // snapshots & freshCopies are fresh
        case Snapshot(_) => true
        case FreshCopy(_) => true

        // For `Let`, it is safe to add `vd` as a fresh binding because we disallow
        // `FieldAssignments` with non-fresh expressions in `check(fd: FunAbstraction)` above.
        // See discussion on: https://github.com/epfl-lara/stainless/pull/985#discussion_r614583479
        case Let(vd, e, b) => rec(e, bindings) && rec(b, bindings + vd)

        // We don't add `vd` as a fresh binding, because it might be reassigned to a non-fresh
        // expression in a `Block` appearing in `b` (see link above)
        case LetVar(vd, e, b) => rec(b, bindings)

        case Block(_, e) => rec(e, bindings)

        case IfExpr(_, e1, e2) => rec(e1, bindings) && rec(e2, bindings)
        case MatchExpr(_, cases) => cases.forall(cse => rec(cse.rhs, bindings))

        //any other expression is conservately assumed to be non-fresh if
        //any sub-expression is non-fresh
        case Operator(args, _) => args.forall(rec(_, bindings))
      })

      rec(expr, Set.empty)
    }

    try {
      // We only check the bodies of functions which are not accessors
      if (!isAccessor(Outer(fd)))
        check(Outer(fd))
      CheckResult.Ok
    } catch {
      case e: ImperativeEliminationException => CheckResult.Error(e)
    }
  }

  def checkSort(sort: ADTSort)(analysis: EffectsAnalysis): Unit = {
    for (fd <- sort.invariant(analysis.symbols)) {
      val invEffects = analysis.effects(fd)
      if (invEffects.nonEmpty)
        throw ImperativeEliminationException(fd, "Invariant has effects on: " + invEffects.head.asString)
    }
  }
}
