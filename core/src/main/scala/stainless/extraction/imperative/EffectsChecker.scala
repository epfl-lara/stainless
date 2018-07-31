/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait EffectsChecker { self: EffectsAnalyzer =>
  import s._

  def checkFunction(fd: FunDef)(symbols: Symbols, effects: EffectsAnalysis): Unit = {
    import symbols._
    import effects._

    def check(fd: FunAbstraction, vds: Set[ValDef]): Unit = {
      checkMutableField(fd)
      checkEffectsLocations(fd)

      if (isGhost(fd)) checkGhostPurity(fd)

      val bindings = vds ++ fd.params
      exprOps.withoutSpecs(fd.fullBody).foreach { bd =>

        // check return value
        if (isMutableType(bd.getType) && !isExpressionFresh(bd)) {
          throw ImperativeEliminationException(bd,
            "Cannot return a shared reference to a mutable object: " + bd)
        }

        object traverser extends inox.transformers.Transformer {
          val trees: self.s.type = self.s
          type Env = Set[ValDef]
          val initEnv = fd.params.toSet

          def rec(e: Expr, bindings: Set[ValDef]): Expr = e match {
            case l @ Let(vd, e, b) if isMutableType(vd.tpe) =>
              if (!isExpressionFresh(e)) try {
                // Check if a precise effect can be computed
                getEffect(e)
              } catch {
                case _: MissformedStainlessCode =>
                  throw ImperativeEliminationException(e, "Illegal aliasing: " + e)
              }
              Let(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetVar(vd, e, b) if isMutableType(vd.tpe) =>
              if (!isExpressionFresh(e))
                throw ImperativeEliminationException(e, "Illegal aliasing: " + e)
              LetVar(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetRec(fds, body) =>
              fds.foreach(fd => check(Inner(fd), bindings))
              LetRec(fds, rec(body, bindings)).copiedFrom(l)

            case l @ Lambda(args, body) =>
              if (isMutableType(body.getType) && !isExpressionFresh(body))
                throw ImperativeEliminationException(l, "Illegal aliasing in lambda body")
              Lambda(args, rec(body, bindings ++ args)).copiedFrom(l)

            case adt @ ADT(id, tps, args) =>
              (adt.getConstructor.sort.definition.tparams zip tps).foreach { case (tdef, instanceType) =>
                if (isMutableType(instanceType) && !(tdef.flags contains IsMutable))
                  throw ImperativeEliminationException(e,
                    "Cannot instantiate a non-mutable type parameter with a mutable type")
              }
              ADT(id, tps, args.map(rec(_, bindings)))

            case Operator(es, recons) => recons(es.map(rec(_, bindings)))
          }
        }

        traverser.transform(bd)
      }
    }

    def checkMutableField(fd: FunAbstraction): Unit = {
      if (fd.flags.exists { case IsField(_) => true case _ => false } && isMutableType(fd.returnType))
        throw ImperativeEliminationException(fd, "A global field cannot refer to a mutable object")
    }

    def checkEffectsLocations(fd: FunAbstraction): Unit = exprOps.preTraversal {
      case Require(pre, _) =>
        val preEffects = effects(pre)
        if (preEffects.nonEmpty)
          throw ImperativeEliminationException(pre, "Precondition has effects on: " + preEffects.head.receiver)

      case Ensuring(_, post @ Lambda(_, body)) =>
        val bodyEffects = effects(body)
        if (bodyEffects.nonEmpty)
          throw ImperativeEliminationException(post, "Postcondition has effects on: " + bodyEffects.head.receiver)

        val oldEffects = effects(exprOps.postMap {
          case Old(e) => Some(e)
          case _ => None
        } (body))
        if (oldEffects.nonEmpty)
          throw ImperativeEliminationException(post, s"Postcondition tries to mutate ${Old(oldEffects.head.receiver)}")

      case Decreases(meas, _) =>
        val measEffects = effects(meas)
        if (measEffects.nonEmpty)
          throw ImperativeEliminationException(meas, "Decreases has effects on: " + measEffects.head.receiver)

      case Assert(pred, _, _) =>
        val predEffects = effects(pred)
        if (predEffects.nonEmpty)
          throw ImperativeEliminationException(pred, "Assertion has effects on: " + predEffects.head.receiver)

      case Forall(_, pred) =>
        val predEffects = effects(pred)
        if (predEffects.nonEmpty)
          throw ImperativeEliminationException(pred, "Quantifier has effects on: " + predEffects.head.receiver)

      case wh @ While(_, _, Some(invariant)) =>
        val invEffects = effects(invariant)
        if (invEffects.nonEmpty)
          throw ImperativeEliminationException(invariant, "Loop invariant has effects on: " + invEffects.head.receiver)

      case m @ MatchExpr(_, cses) =>
        cses.foreach { cse =>
          cse.optGuard.foreach { guard =>
            val guardEffects = effects(guard)
            if (guardEffects.nonEmpty)
              throw ImperativeEliminationException(guard, "Pattern guard has effects on: " + guardEffects.head.receiver)
          }

          patternOps.preTraversal {
            case up: UnapplyPattern =>
              val upEffects = effects(Outer(up.getFunction.fd))
              if (upEffects.nonEmpty)
                throw ImperativeEliminationException(up, "Pattern unapply has effects on: " + upEffects.head.receiver)

            case _ => ()
          }(cse.pattern)
        }

      case _ => ()
    }(fd.fullBody)

    def isGhost(fd: FunAbstraction): Boolean = fd.flags.contains(Ghost)

    def checkGhostPurity(fd: FunAbstraction): Unit = {
      val effs = effects(fd.fullBody)

      if (effs.exists(eff => !validGhostEffects(eff)))
        throw ImperativeEliminationException(fd, s"Ghost function cannot have effect on non-ghost state")
    }

    def validGhostEffects(eff: Effect) = eff match {
      case Effect(rec, target) => isGhostTarget(rec, target.path)
    }

    def isGhostTarget(rec: Expr, path: Seq[Accessor]): Boolean = {
      def go(expr: Expr, path: Seq[Accessor]): Boolean = path match {
        case FieldAccessor(selector) +: rest =>
          val tpe @ ADTType(_, _) = expr.getType(symbols)
          val field = tpe.getField(selector).get
          field.flags.contains(Ghost) && go(ADTSelector(expr, selector), rest)

        case ArrayAccessor(index) +: rest =>
          go(ArraySelect(expr, index), rest)

        case Seq() => true
      }

      go(rec, path)
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

        //function invocation always return a fresh expression, by hypothesis (global assumption)
        case (_: FunctionInvocation | _: ApplyLetRec | _: Application) => true

        //ArrayUpdated returns a mutable array, which by definition is a clone of the original
        case ArrayUpdated(IsTyped(_, ArrayType(base)), _, _) => !isMutableType(base)

        // These cases cover some limitations due to dotty inlining
        case Let(vd, e, b) => rec(e, bindings) && rec(b, bindings + vd)
        case LetVar(vd, e, b) => rec(e, bindings) && rec(b, bindings + vd)

        case Block(_, e) => rec(e, bindings)

        //any other expression is conservately assumed to be non-fresh if
        //any sub-expression is non-fresh (i.e. an if-then-else with a reference in one branch)
        case Operator(args, _) => args.forall(rec(_, bindings))
      })

      rec(expr, Set.empty)
    }

    check(Outer(fd), Set.empty)
  }

  def checkSort(sort: ADTSort)(symbols: Symbols, effects: EffectsAnalysis): Unit = {
    import symbols._

    for (fd <- sort.invariant) {
      val invEffects = effects(fd)
      if (invEffects.nonEmpty)
        throw ImperativeEliminationException(fd, "Invariant has effects on: " + invEffects.head)
    }
  }
}
