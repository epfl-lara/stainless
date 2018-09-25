/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait GhostChecker { self: EffectsAnalyzer =>
  import s._

  protected def checkGhost(fd: FunDef)(symbols: Symbols, effects: EffectsAnalysis): Unit = {
    import symbols._
    import effects._

    def isGhostEffect(effect: Effect): Boolean = {
      def rec(tpe: Type, path: Seq[Accessor]): Boolean = (tpe, path) match {
        case (adt: ADTType, FieldAccessor(selector) +: rest) =>
          val field = adt.getField(selector).get
          (field.flags contains Ghost) || rec(field.getType, rest)

        case (ArrayType(base), ArrayAccessor(index) +: rest) =>
          rec(base, rest)

        case _ => false
      }

      (effect.receiver.flags contains Ghost) || rec(effect.receiver.getType, effect.target.path)
    }

    def isGhostExpression(e: Expr): Boolean = e match {
      case v: Variable => v.flags contains Ghost

      case FunInvocation(id, _, args, _) =>
        val fun = lookupFunction(id).map(Outer(_)).getOrElse(effects.local(id))
        (fun.flags contains Ghost) ||
        (fun.params zip args).exists { case (vd, arg) =>
          !(vd.flags contains Ghost) && isGhostExpression(arg)
        }

      case ADT(id, _, args) =>
        (getConstructor(id).fields zip args).exists { case (vd, arg) =>
          !(vd.flags contains Ghost) && isGhostExpression(arg)
        }

      case sel @ ADTSelector(e, id) =>
        isGhostExpression(e) ||
        (sel.constructor.fields.find(_.id == id).get.flags contains Ghost)

      case Let(vd, e, b) => isGhostExpression(b)
      case LetVar(vd, e, b) => isGhostExpression(b)
      case Assignment(_, _) => false
      case FieldAssignment(_, _, _) => false
      case Block(_, e) => isGhostExpression(e)

      case Operator(es, _) => es.exists(isGhostExpression)
    }

    def checkFunction(fun: FunAbstraction, inGhost: Boolean): Unit = {
      if (fun.flags contains Ghost) {
        if (!effects(fun).forall(isGhostEffect))
          throw ImperativeEliminationException(fun, s"Ghost function cannot have effect on non-ghost state")
        new Checker(true).traverse(fun)
      } else {
        if (!inGhost && isGhostExpression(fun.fullBody))
          throw ImperativeEliminationException(fun, s"Non-ghost function cannot return a ghost result")
        new Checker(inGhost).traverse(fun)
      }
    }

    class Checker(inGhost: Boolean) extends TreeTraverser {
      override def traverse(expr: Expr): Unit = expr match {
        case Let(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case Let(vd, e, b) if !(vd.flags contains Ghost) && inGhost =>
          val newVd = vd.copy(flags = vd.flags :+ Ghost)
          traverse(Let(newVd, e, exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), b)).copiedFrom(expr))

        case Let(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case LetVar(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case LetVar(vd, e, b) if !(vd.flags contains Ghost) && inGhost =>
          val newVd = vd.copy(flags = vd.flags :+ Ghost)
          traverse(LetVar(newVd, e, exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), b)).copiedFrom(expr))

        case LetVar(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case Assignment(v, e) if (v.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable assignment must only have effects on ghost fields")

        case Assignment(v, e) if !(v.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable assignment cannot be ghost")

        case FieldAssignment(obj, id, e) if (
          isGhostExpression(ADTSelector(obj, id)) &&
          !effects(e).forall(isGhostEffect)
        ) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost field assignment must only have effects on ghost fields")

        case FieldAssignment(obj, id, e) if (
          !isGhostExpression(ADTSelector(obj, id)) &&
          isGhostExpression(e)
        ) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost field assignment cannot be ghost")

        case l @ Lambda(params, body) if params.exists(_.flags contains Ghost) =>
          throw ImperativeEliminationException(expr, "Lambdas cannot have ghost parameters")

        case LetRec(fds, body) =>
          fds.foreach(fd => checkFunction(Inner(fd), inGhost))
          traverse(body)

        case FunInvocation(id, tps, args, _) =>
          traverse(id)
          tps.foreach(traverse)

          (lookupFunction(id).map(Outer(_)).getOrElse(effects.local(id)).params zip args)
            .foreach { case (vd, arg) =>
              if (vd.flags contains Ghost) {
                if (!effects(arg).forall(isGhostEffect))
                  throw ImperativeEliminationException(arg,
                    s"Argument to ghost parameter `${vd.id}` of `${id}` must only have effects on ghost fields")
                new Checker(true).traverse(arg)
              } else {
                traverse(arg)
              }
            }

        case adt @ ADT(id, tps, args) =>
          traverse(id)
          tps.foreach(traverse)

          (adt.getConstructor.fields zip args)
            .foreach { case (vd, arg) =>
              if (vd.flags contains Ghost) {
                if (!effects(arg).forall(isGhostEffect))
                  throw ImperativeEliminationException(arg,
                    s"Argument to ghost field `${vd.id}` of class `${id}` must only have effects on ghost fields")
                new Checker(true).traverse(arg)
              } else {
                traverse(arg)
              }
            }

        case _ => super.traverse(expr)
      }

      def traverse(fun: s.FunAbstraction): Unit = {
        traverse(fun.id)
        fun.tparams.foreach(traverse)
        fun.params.foreach(traverse)
        traverse(fun.returnType)
        traverse(fun.fullBody)
        fun.flags.foreach(traverse)
      }
    }

    checkFunction(Outer(fd), false)
  }
}
