/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait GhostChecker { self: EffectsAnalyzer =>
  import s._

  protected def checkGhost(fd: FunDef)(symbols: Symbols, effects: EffectsAnalysis): Unit = {
    import symbols._
    import effects._

    def checkGhostFunction(fun: FunAbstraction): Unit = {
      if ((fun.flags contains Ghost) && !effects(fun).forall(isGhostEffect))
        throw ImperativeEliminationException(fun, s"Ghost function cannot have effect on non-ghost state")
    }

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

    def checkEffects(fd: FunDef): Unit = new TreeTraverser {
      override def traverse(expr: Expr): Unit = expr match {
        case l @ Let(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case l @ LetVar(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case Assignment(v, e) if (v.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost variable assignment must only have effects on ghost fields")

        case FieldAssignment(obj, id, e) if (
          isGhostExpression(ADTSelector(obj, id)) &&
          !effects(e).forall(isGhostEffect)
        ) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of ghost field assignment must only have effects on ghost fields")

        case l @ Lambda(params, body) if params.exists(_.flags contains Ghost) =>
          throw ImperativeEliminationException(expr, "Lambdas cannot have ghost parameters")

        case LetRec(fds, body) =>
          fds.foreach(fd => checkGhostFunction(Inner(fd)))
          super.traverse(expr)

        case FunInvocation(id, _, args, _) =>
          val fun = lookupFunction(id).map(Outer(_)).getOrElse(effects.local(id))
          (fun.params zip args)
            .filter { case (vd, arg) => (vd.flags contains Ghost) && !effects(arg).forall(isGhostEffect) }
            .foreach { case (vd, arg) =>
              throw ImperativeEliminationException(arg,
                s"Argument to ghost parameter `${vd.id}` of `${id}` must only have effects on ghost fields")
            }

          super.traverse(expr)

        case adt @ ADT(id, tps, args) =>
          (adt.getConstructor.fields zip args)
            .filter { case (vd, arg) => (vd.flags contains Ghost) && !effects(arg).forall(isGhostEffect) }
            .foreach { case (vd, arg) =>
              throw ImperativeEliminationException(arg,
                s"Argument to ghost field `${vd.id}` of class `${id}` must only have effects on ghost fields")
            }

          super.traverse(expr)

        case _ => super.traverse(expr)
      }
    }.traverse(fd)


    def checkNonGhostFunction(fun: FunAbstraction): Unit = {
      if (!(fun.flags contains Ghost) && isGhostExpression(fun.fullBody))
        throw ImperativeEliminationException(fun, s"Non-ghost function cannot return a ghost result")
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

    def checkExpressions(fd: FunDef): Unit = new TreeTraverser {
      override def traverse(expr: Expr): Unit = expr match {
        case Let(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case LetVar(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case Assignment(v, e) if !(v.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable assignment cannot be ghost")

        case FieldAssignment(obj, id, e) if (
          !isGhostExpression(ADTSelector(obj, id)) &&
          isGhostExpression(e)
        ) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost field assignment cannot be ghost")

        case LetRec(fds, _) =>
          fds.foreach(fd => checkNonGhostFunction(Inner(fd)))
          super.traverse(expr)

        case _ => super.traverse(expr)
      }
    }.traverse(fd)

    checkGhostFunction(Outer(fd))
    checkNonGhostFunction(Outer(fd))
    checkEffects(fd)
    checkExpressions(fd)
  }
}
