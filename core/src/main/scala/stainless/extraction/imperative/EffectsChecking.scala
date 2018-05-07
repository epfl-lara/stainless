/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait EffectsChecking { self =>
  val trees: Trees
  import trees._

  def checkEffects(effects: EffectsAnalysis { val trees: self.trees.type }): Unit = {
    implicit val s = effects.symbols
    import effects.symbols._

    def checkFunction(fd: FunAbstraction, vds: Set[ValDef]): Unit = {
      checkMutableField(fd)
      checkEffectsLocations(fd)

      val bindings = vds ++ fd.params
      exprOps.withoutSpecs(fd.fullBody).foreach { bd =>

        // check return value
        if (effects.isMutableType(bd.getType) && !isExpressionFresh(bd)) {
          throw ImperativeEliminationException(bd,
            "Cannot return a shared reference to a mutable object: " + bd)
        }

        object traverser extends inox.transformers.Transformer {
          val trees: self.trees.type = self.trees
          type Env = Set[ValDef]
          val initEnv = fd.params.toSet

          def rec(e: Expr, bindings: Set[ValDef]): Expr = e match {
            case l @ Let(vd, e, b) if effects.isMutableType(vd.tpe) =>
              if (!isExpressionFresh(e))
                throw ImperativeEliminationException(e, "Illegal aliasing: " + e)
              Let(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetVar(vd, e, b) if effects.isMutableType(vd.tpe) =>
              if (!isExpressionFresh(e))
                throw ImperativeEliminationException(e, "Illegal aliasing: " + e)
              LetVar(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetRec(fds, body) =>
              fds.foreach(fd => checkFunction(Inner(fd), bindings))
              LetRec(fds, rec(body, bindings)).copiedFrom(l)

            case l @ Lambda(args, body) =>
              if (effects.isMutableType(body.getType) && !isExpressionFresh(body))
                throw ImperativeEliminationException(l, "Illegal aliasing in lambda body")
              Lambda(args, rec(body, bindings ++ args)).copiedFrom(l)

            case adt @ ADT(id, tps, args) =>
              (adt.getConstructor.sort.definition.tparams zip tps).foreach { case (tdef, instanceType) =>
                if (effects.isMutableType(instanceType) && !(tdef.flags contains IsMutable))
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
      if (fd.flags.exists { case IsField(_) => true case _ => false } && effects.isMutableType(fd.returnType))
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
      def rec(expr: Expr, bindings: Set[ValDef]): Boolean = !effects.isMutableType(expr.getType) || (expr match {
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
        case ArrayUpdated(IsTyped(_, ArrayType(base)), _, _) => !effects.isMutableType(base)

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

    for (fd <- effects.symbols.functions.values) {
      checkFunction(Outer(fd), Set.empty)
    }

    for (sort <- effects.symbols.sorts.values; fd <- sort.invariant) {
      val invEffects = effects(fd)
      if (invEffects.nonEmpty)
        throw ImperativeEliminationException(fd, "Invariant has effects on: " + invEffects.head)
    }
  }
}
