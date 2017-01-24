/* Copyright 2009-2016 EPFL, Lausanne */

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
      checkPureAnnotation(fd)
      checkMutableField(fd)
      checkEffectsLocations(fd)

      val bindings = vds ++ fd.params
      exprOps.withoutSpec(fd.body).foreach { bd =>

        // check return value
        effects.getReturnedExpressions(bd).foreach { expr =>
          if (effects.isMutableType(expr.getType)) {
            effects.getReceiverVariable(expr).foreach(v =>
              if (bindings.contains(v.toVal))
                throw ImperativeEliminationException(expr.getPos, "Cannot return a shared reference to a mutable object: " + expr)
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
                throw ImperativeEliminationException(e.getPos, "Illegal aliasing: " + e)
              Let(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetVar(vd, e, b) if effects.isMutableType(vd.tpe) =>
              if (!isExpressionFresh(e))
                throw ImperativeEliminationException(e.getPos, "Illegal aliasing: " + e)
              LetVar(vd, rec(e, bindings), rec(b, bindings + vd)).copiedFrom(l)

            case l @ LetRec(fds, body) =>
              fds.foreach(fd => checkFunction(Inner(fd), bindings))
              LetRec(fds.map { case LocalFunDef(vd, tparams, body) =>
                LocalFunDef(vd, tparams, rec(body, bindings).asInstanceOf[Lambda])
              }, rec(body, bindings)).copiedFrom(l)

            case ADT(adt, args) =>
              adt.getADT.definition.tparams.zip(adt.tps).foreach { case (tdef, instanceType) =>
                if (effects.isMutableType(instanceType) && !(tdef.flags contains IsMutable))
                  throw ImperativeEliminationException(e.getPos, "Cannot instantiate a non-mutable type parameter with a mutable type")
              }
              ADT(adt, args.map(rec(_, bindings)))

            case Operator(es, recons) => recons(es.map(rec(_, bindings)))
          }
        }

        traverser.transform(bd)
      }
    }


    /* Checks and reports error if a function is annotated as pure and still has effects.
     * Maybe it would be good in the future to merge this @pure annotation with the report
     * from the AnalysisPhase, but until a good design is found we just implement this quick
     * error reporting here.
     */
    def checkPureAnnotation(fd: FunAbstraction): Unit = {
      if (fd.flags contains IsPure) {
        if (effects(fd).nonEmpty) {
          throw ImperativeEliminationException(fd.getPos, "Function annotated @pure has effects.")
        }
      }
    }


    def checkMutableField(fd: FunAbstraction): Unit = {
      if (false) // FIXME fd.flags.exists { case IsField(_) => true case _ => false } && effects.isMutableType(fd.returnType))
        throw ImperativeEliminationException(fd.getPos, "A global field cannot refer to a mutable object")
    }


    def checkEffectsLocations(fd: FunAbstraction): Unit = {
      exprOps.postconditionOf(fd.body).foreach { case post @ Lambda(vds, body) =>
        val bodyEffects = effects(body)
        if (bodyEffects.nonEmpty)
          throw ImperativeEliminationException(post.getPos, "Postcondition has effects on: " + bodyEffects.head)
      }

      exprOps.preconditionOf(fd.body).foreach { pre =>
        val preEffects = effects(pre)
        if (preEffects.nonEmpty)
          throw ImperativeEliminationException(pre.getPos, "Precondition has effects on: " + preEffects.head)
      }

      exprOps.withoutSpec(fd.body).foreach { body =>
        exprOps.preTraversal {
          case Assert(pred, _, _) =>
            val predEffects = effects(pred)
            if (predEffects.nonEmpty)
              throw ImperativeEliminationException(pred.getPos, "Assertion has effects on: " + predEffects.head)

          case wh @ While(_, _, Some(invariant)) =>
            val invEffects = effects(invariant) 
            if (invEffects.nonEmpty)
              throw ImperativeEliminationException(invariant.getPos, "Loop invariant has effects on: " + invEffects.head)

          case m @ MatchExpr(_, cses) =>
            cses.foreach { cse =>
              cse.optGuard.foreach { guard =>
                val guardEffects = effects(guard)
                if (guardEffects.nonEmpty)
                  throw ImperativeEliminationException(guard.getPos, "Pattern guard has effects on: " + guardEffects.head)
              }

              patternOps.preTraversal {
                case up: UnapplyPattern =>
                  val upEffects = effects(Outer(up.tfd.fd))
                  if (upEffects.nonEmpty)
                    throw ImperativeEliminationException(up.getPos, "Pattern unapply has effects on: " + upEffects.head)

                case _ => ()
              }(cse.pattern)
            }

          case _ => ()
        }(body)
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
      !effects.isMutableType(expr.getType) || (expr match {
        case v: Variable => false
        case ADT(_, args) => args.forall(isExpressionFresh)

        case FiniteArray(elems, _) => elems.forall(isExpressionFresh)
        case LargeArray(elems, default, _, _) => elems.forall(p => isExpressionFresh(p._2)) && isExpressionFresh(default)

        //function invocation always return a fresh expression, by hypothesis (global assumption)
        case FunctionInvocation(_, _, _) => true

        //ArrayUpdated returns a mutable array, which by definition is a clone of the original
        case ArrayUpdated(_, _, _) => true

        //any other expression is conservately assumed to be non-fresh if
        //any sub-expression is non-fresh (i.e. an if-then-else with a reference in one branch)
        case Operator(args, _) => args.forall(isExpressionFresh)
      })
    }

    for (fd <- effects.symbols.functions.values) {
      checkFunction(Outer(fd), Set.empty)
    }

    for (adt <- effects.symbols.adts.values; fd <- adt.invariant) {
      val invEffects = effects(fd)
      if (invEffects.nonEmpty)
        throw ImperativeEliminationException(fd.getPos, "Invariant has effects on: " + invEffects.head)
    }
  }
}
