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

    object traverser extends TreeTraverser {
      override def traverse(e: Expr): Unit = e match {
        case l @ Let(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(e,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case l @ LetVar(vd, e, b) if (vd.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(e,
            "Right-hand side of ghost variable must only have effects on ghost fields")

        case Assignment(v, e) if (v.flags contains Ghost) && !effects(e).forall(isGhostEffect) =>
          throw ImperativeEliminationException(e,
            "Right-hand side of ghost variable assignment must only have effects on ghost fields")

        case l @ Lambda(params, body) if params.exists(_.flags contains Ghost) =>
          throw ImperativeEliminationException(e, "Lambdas cannot have ghost parameters")

        case LetRec(fds, body) =>
          fds.foreach(fd => checkGhostFunction(Inner(fd)))
          super.traverse(e)

        case fi @ FunctionInvocation(id, tps, args) if fi.tfd.params.exists(_.flags contains Ghost) =>
          (fi.tfd.params zip args)
            .filter { case (vd, arg) => (vd.flags contains Ghost) && !effects(arg).forall(isGhostEffect) }
            .foreach { case (vd, arg) =>
              throw ImperativeEliminationException(arg,
                s"Argument to ghost parameter `${vd.id}` of `${fi.id}` must only have effects on ghost fields")
            }

          super.traverse(fi)

        case ApplyLetRec(v, _, _, args) if effects.local(v.id).params.exists(_.flags contains Ghost) =>
          (effects.local(v.id).params zip args)
            .filter { case (vd, arg) => (vd.flags contains Ghost) && !effects(arg).forall(isGhostEffect) }
            .foreach { case (vd, arg) =>
              throw ImperativeEliminationException(arg,
                s"Argument to ghost parameter `${vd.id}` of `${v.id}` must only have effects on ghost fields")
            }

          super.traverse(e)

        case adt @ ADT(id, tps, args) =>
          adt.getConstructor.fields.zip(args)
            .filter { case (vd, arg) => (vd.flags contains Ghost) && !effects(arg).forall(isGhostEffect) }
            .foreach { case (vd, arg) =>
              throw ImperativeEliminationException(arg,
                s"Argument to ghost field `${vd.id}` of class `${id}` must only have effects on ghost fields")
            }

          super.traverse(adt)

        case _ => super.traverse(e)
      }
    }

    checkGhostFunction(Outer(fd))
    traverser.traverse(fd)
  }
}
