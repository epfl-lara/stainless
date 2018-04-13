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
        effects.getReturnedExpressions(bd).foreach { expr =>
          if (effects.isMutableType(expr.getType)) {
            effects.getReceiverVariable(expr).foreach(v =>
              if (bindings.contains(v.toVal))
                throw ImperativeEliminationException(expr, "Cannot return a shared reference to a mutable object: " + expr)
            )
          }
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
              LetRec(fds.map { case LocalFunDef(vd, tparams, body) =>
                LocalFunDef(vd, tparams, rec(body, bindings).asInstanceOf[Lambda])
              }, rec(body, bindings)).copiedFrom(l)

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
          throw ImperativeEliminationException(pre, "Precondition has effects on: " + preEffects.head)

      case Ensuring(_, post @ Lambda(_, body)) =>
        val bodyEffects = effects(body)
        if (bodyEffects.nonEmpty)
          throw ImperativeEliminationException(post, "Postcondition has effects on: " + bodyEffects.head)

        val oldEffects = effects(exprOps.postMap {
          case Old(e) => Some(e)
          case _ => None
        } (body))
        if (oldEffects.nonEmpty)
          throw ImperativeEliminationException(post, s"Postcondition tries to mutate ${Old(oldEffects.head)}")

      case Decreases(meas, _) =>
        val measEffects = effects(meas)
        if (measEffects.nonEmpty)
          throw ImperativeEliminationException(meas, "Decreases has effects on: " + measEffects.head)

      case Assert(pred, _, _) =>
        val predEffects = effects(pred)
        if (predEffects.nonEmpty)
          throw ImperativeEliminationException(pred, "Assertion has effects on: " + predEffects.head)

      case wh @ While(_, _, Some(invariant)) =>
        val invEffects = effects(invariant)
        if (invEffects.nonEmpty)
          throw ImperativeEliminationException(invariant, "Loop invariant has effects on: " + invEffects.head)

      case m @ MatchExpr(_, cses) =>
        cses.foreach { cse =>
          cse.optGuard.foreach { guard =>
            val guardEffects = effects(guard)
            if (guardEffects.nonEmpty)
              throw ImperativeEliminationException(guard, "Pattern guard has effects on: " + guardEffects.head)
          }

          patternOps.preTraversal {
            case up: UnapplyPattern =>
              val upEffects = effects(Outer(up.getFunction.fd))
              if (upEffects.nonEmpty)
                throw ImperativeEliminationException(up, "Pattern unapply has effects on: " + upEffects.head)

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
      !effects.isMutableType(expr.getType) || (expr match {
        case v: Variable => false
        case ADT(_, _, args) => args.forall(isExpressionFresh)

        case FiniteArray(elems, _) => elems.forall(isExpressionFresh)
        case LargeArray(elems, default, _, _) => elems.forall(p => isExpressionFresh(p._2)) && isExpressionFresh(default)

        // We assume `old(.)` is fresh here, although such cases will probably be
        // rejected later in `ImperativeCleanup`.
        case Old(_) => true

        //function invocation always return a fresh expression, by hypothesis (global assumption)
        case FunctionInvocation(_, _, _) => true

        //ArrayUpdated returns a mutable array, which by definition is a clone of the original
        case ArrayUpdated(_, _, _) => true

        // These cases cover some limitations due to dotty inlining
        case Let(vd, e, v: Variable) if vd == v.toVal => isExpressionFresh(e)
        case Let(vd, e, Assume(pred, v: Variable)) if vd == v.toVal => isExpressionFresh(e)

        //any other expression is conservately assumed to be non-fresh if
        //any sub-expression is non-fresh (i.e. an if-then-else with a reference in one branch)
        case Operator(args, _) => args.forall(isExpressionFresh)
      })
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
