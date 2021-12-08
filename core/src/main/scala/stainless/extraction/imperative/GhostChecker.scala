/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait GhostChecker { self: EffectsAnalyzer =>
  import s._

  protected def checkGhost(fd: FunDef)(analysis: EffectsAnalysis): Unit = {
    import analysis.{given, _}
    import symbols.{given, _}

    def isGhostEffect(effect: Effect): Boolean = {
      def rec(tpe: Type, path: Seq[Accessor]): Boolean = (tpe, path) match {
        case (adt: ADTType, ADTFieldAccessor(selector) +: rest) =>
          val field = adt.getField(selector).get
          (field.flags contains Ghost) || rec(field.getType, rest)

        case (ct: ClassType, ClassFieldAccessor(selector) +: rest) =>
          getClassField(ct, selector) match {
            case Some(field) =>
              (field.flags contains Ghost) || rec(field.getType, rest)
            case None =>
              throw ImperativeEliminationException(fd,
                s"Could not find field $selector of class/trait ${ct.id}")
          }

        case (ArrayType(base), ArrayAccessor(index) +: rest) =>
          rec(base, rest)

        case (tt: TupleType, TupleFieldAccessor(index) +: rest) =>
          rec(tt.bases(index - 1), rest)

        case _ => false
      }

      (effect.receiver.flags contains Ghost) || rec(effect.receiver.getType, effect.path.toSeq)
    }

    def isGhostExpression(e: Expr): Boolean = e match {
      case v: Variable => v.flags contains Ghost

      // This will typically be the case for contracts from `stainless.lang.StaticChecks`
      case Annotated(e, flags) if flags contains Ghost => false

      // Measures are also considered ghost, as they are never executed
      case Decreases(_, body) => isGhostExpression(body)

      case Snapshot(_) => true
      case FreshCopy(e) => isGhostExpression(e)

      case FunInvocation(id, _, args, _) =>
        val fun = lookupFunction(id).map(Outer(_)).getOrElse(analysis.local(id))
        (fun.flags contains Ghost) ||
        (fun.params zip args).exists { case (vd, arg) =>
          !(vd.flags contains Ghost) && isGhostExpression(arg)
        }

      case ADT(id, _, args) =>
        (getConstructor(id).fields zip args).exists { case (vd, arg) =>
          !(vd.flags contains Ghost) && isGhostExpression(arg)
        }

      case ClassConstructor(ct, args) =>
        (ct.tcd.fields zip args).exists { case (vd, arg) =>
          !(vd.flags contains Ghost) && isGhostExpression(arg)
        }

      case sel @ ADTSelector(e, id) =>
        isGhostExpression(e) ||
        (sel.constructor.fields.find(_.id == id).get.flags contains Ghost)

      case sel @ ClassSelector(e, id) =>
        isGhostExpression(e) ||
        (sel.field.get.flags contains Ghost)

      case Let(vd, e, b) => isGhostExpression(b)
      case LetVar(vd, e, b) => isGhostExpression(b)
      case Assignment(_, _) => false
      case FieldAssignment(_, _, _) => false
      case Block(_, e) => isGhostExpression(e)

      case Operator(es, _) => es.exists(isGhostExpression)
    }

    def checkFunction(fun: FunAbstraction, inGhost: Boolean): Unit = {
      if (fun.flags contains Synthetic) {
        () // Synthetic functions should always be fine with respect to ghost flow
      } else if (fun.flags contains Ghost) {
        effects(fun).find(!isGhostEffect(_)) match {
          case Some(eff) => throw ImperativeEliminationException(fun, s"Ghost function ${fun.id.asString} cannot have effect on non-ghost state: ${eff.targetString}")
          case None => ()
        }
        new Checker(true).traverse(fun)
      } else {
        if (!inGhost && isGhostExpression(fun.fullBody))
          throw ImperativeEliminationException(fun, s"Non-ghost function ${fun.id.asString} cannot return a ghost result")
        new Checker(inGhost).traverse(fun)
      }
    }

    class Checker(inGhost: Boolean) extends ConcreteOOSelfTreeTraverser {

      private[this] def isADT(e: Expr): Boolean = e.getType match {
        case _: ADTType => true
        case _ => false
      }

      private[this] def isObject(e: Expr): Boolean = e.getType match {
        case _: ClassType => true
        case _ => false
      }

      override def traverse(expr: Expr): Unit = expr match {
        case Let(vd, e, b) if vd.flags contains Ghost =>
          effects(e).find(!isGhostEffect(_)) match {
            case Some(eff) =>
              throw ImperativeEliminationException(expr,
                s"Right-hand side of ghost variable must only have effects on ghost fields (${eff.targetString} is not ghost)")
            case None =>
              traverse(vd)
              new Checker(true).traverse(e)
              traverse(b)
          }

        case Let(vd, e, b) if !(vd.flags contains Ghost) && inGhost =>
          val newVd = vd.copy(flags = vd.flags :+ Ghost)
          traverse(Let(newVd, e, exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), b)).copiedFrom(expr))

        case Let(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case LetVar(vd, e, b) if vd.flags contains Ghost =>
          effects(e).find(!isGhostEffect(_)) match {
            case Some(eff) =>
              throw ImperativeEliminationException(expr,
                s"Right-hand side of ghost variable must only have effects on ghost fields (${eff.targetString} is not ghost)")
            case None =>
              traverse(vd)
              new Checker(true).traverse(e)
              traverse(b)
          }

        case LetVar(vd, e, b) if !(vd.flags contains Ghost) && inGhost =>
          val newVd = vd.copy(flags = vd.flags :+ Ghost)
          traverse(LetVar(newVd, e, exprOps.replaceFromSymbols(Map(vd -> newVd.toVariable), b)).copiedFrom(expr))

        case LetVar(vd, e, _) if !(vd.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable cannot be ghost")

        case Assignment(v, e) if v.flags contains Ghost =>
          effects(e).find(!isGhostEffect(_)) match {
            case Some(eff) =>
              throw ImperativeEliminationException(expr,
                s"Right-hand side of ghost variable assignment must only have effects on ghost fields (${eff.targetString} is not ghost)")
            case None =>
              traverse(v)
              new Checker(true).traverse(e)
          }

        case Assignment(v, e) if !(v.flags contains Ghost) && isGhostExpression(e) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost variable assignment cannot be ghost")

        case Snapshot(e) if !inGhost =>
          throw ImperativeEliminationException(expr,
            "Snapshots can only be used in ghost contexts")

        case FieldAssignment(obj, id, e) if isADT(obj) && isGhostExpression(ADTSelector(obj, id)) =>
          effects(e).find(!isGhostEffect(_)) match {
            case Some(eff) =>
              throw ImperativeEliminationException(expr,
                s"Right-hand side of ghost field assignment must only have effects on ghost fields (${eff.targetString} is not ghost)")
            case None =>
              traverse(obj)
              traverse(id)
              new Checker(true).traverse(e)
          }

        case FieldAssignment(obj, id, e) if isObject(obj) && isGhostExpression(ClassSelector(obj, id)) =>
          effects(e).find(!isGhostEffect(_)) match {
            case Some(eff) =>
              throw ImperativeEliminationException(expr,
                s"Right-hand side of ghost field assignment must only have effects on ghost fields (${eff.targetString} is not ghost)")
            case None =>
              traverse(obj)
              traverse(id)
              new Checker(true).traverse(e)
          }

        case FieldAssignment(obj, id, e) if (
          isObject(obj) &&
          !isGhostExpression(ClassSelector(obj, id)) &&
          isGhostExpression(e)
        ) =>
          throw ImperativeEliminationException(expr,
            "Right-hand side of non-ghost field assignment cannot be ghost")

        case l @ Lambda(params, body) if params.exists(_.flags contains Ghost) =>
          throw ImperativeEliminationException(expr, "Lambdas cannot have ghost parameters")

        case LetRec(fds, body) =>
          fds.foreach(fd => checkFunction(Inner(fd), inGhost))
          traverse(body)

        case Annotated(e, flags) if flags contains Ghost =>
          new Checker(true).traverse(e)

        case FunInvocation(id, tps, args, _) =>
          traverse(id)
          tps.foreach(traverse)

          (lookupFunction(id).map(Outer(_)).getOrElse(analysis.local(id)).params zip args)
            .foreach { case (vd, arg) =>
              if (vd.flags contains Ghost) {
                effects(arg).find(!isGhostEffect(_)) match {
                  case Some(eff) =>
                    throw ImperativeEliminationException(arg,
                      s"Argument to ghost parameter `${vd.id}` of `${id}` must only have effects on ghost fields (${eff.targetString} is not ghost)")
                  case None =>
                    new Checker(true).traverse(arg)
                }
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
                    s"Argument to ghost field `${vd.id.asString}` of class `${id.asString}` must only have effects on ghost fields")
                new Checker(true).traverse(arg)
              } else {
                traverse(arg)
              }
            }

        case cons @ ClassConstructor(ct, args) =>
          traverse(ct)

          (ct.tcd.fields zip args)
            .foreach { case (vd, arg) =>
              if (vd.flags contains Ghost) {
                if (!effects(arg).forall(isGhostEffect))
                  throw ImperativeEliminationException(arg,
                    s"Argument to ghost field `${vd.id.asString}` of class `${ct.id.asString}` must only have effects on ghost fields")
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
