/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class ChooseEncoder(override val s: Trees, override val t: Trees)
                   (using override val context: inox.Context)
  extends CachingPhase with SimplyCachedFunctions with IdentitySorts { self =>

  type TransformerContext = s.Symbols
  override def getContext(symbols: s.Symbols) = symbols

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected def extractFunction(context: TransformerContext, fd: s.FunDef): Seq[t.FunDef] = {
    var fdChooses = Seq[t.FunDef]()

    object ce extends inox.transformers.Transformer {
      override val s: self.s.type = self.s
      override val t: self.t.type = self.t

      type Env = Seq[t.ValDef]

      import t._ // for implicit `VariableConverter`, required for `replaceFromSymbols`

      def transform(fd: s.FunDef): t.FunDef = {
        val params2 = fd.params.map(transform(_, Seq()))
        new t.FunDef(
          fd.id,
          fd.tparams.map(transform(_, Seq())),
          params2,
          transform(fd.returnType, params2),
          transform(fd.fullBody, params2),
          fd.flags.map(transform(_, Seq()))
        ).setPos(fd)
      }

      override def transform(e: s.Expr, env: Seq[t.ValDef]): t.Expr = e match {
        case s.Let(vd, expr, body) =>
          val newVd = transform(vd, env)
          t.Let(newVd, transform(expr, env),
            transform(body, env :+ newVd)
          ).copiedFrom(e)

        case s.Lambda(params, body) =>
          val (newParams, newEnv) = params.foldLeft((Seq[t.ValDef](), env)) {
            case ((accParams, accEnv), vd) =>
              val newVd = transform(vd, accEnv)
              (accParams :+ newVd, accEnv :+ newVd)
          }
          t.Lambda(newParams, transform(body, newEnv)).copiedFrom(e)

        case c @ s.Choose(vd, pred) =>
          val (substMap, freshParams) = env.foldLeft((Map[t.ValDef, t.Expr](), Seq[t.ValDef]())) {
            case ((substMap, vds), vd) =>
              val ntpe = t.typeOps.replaceFromSymbols(substMap, vd.tpe)
              val nvd = t.ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
              (substMap + (vd -> nvd.toVariable), vds :+ nvd)
          }

          val returnType = t.typeOps.replaceFromSymbols(substMap, transform(vd.tpe, env))
          val newVd = transform(vd, env).copy(tpe = returnType).setPos(vd)
          val newPred = exprOps.replaceFromSymbols(substMap, transform(pred, env :+ newVd))
          val newChoose = Choose(newVd, newPred).copiedFrom(c)

          val newFd = new t.FunDef(
            FreshIdentifier("choose", true), fd.tparams.map(transform(_, env)), freshParams,
            returnType,
            newChoose,
            Seq(t.Derived(Some(fd.id)), t.DropVCs),
          ).setPos(fd)

          fdChooses = fdChooses :+ newFd

          val fi = t.FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), env.map(_.toVariable)).copiedFrom(c)
          if (vd.flags.contains(s.DropVCs))
            fi
          else
            t.Assert(
              t.Not(t.Forall(Seq(transform(vd, env)), t.Not(transform(pred, env)).setPos(c)).setPos(c)).setPos(c),
              Some("Choose satisfiability"),
              fi
            ).setPos(c)

        case _ => super.transform(e, env)
      }
    }


    // bind `newFd` before returning so that `fdChooses` gets filled with the new `choose` functions
    val newFd = ce.transform(fd)
    fdChooses :+ newFd
  }

}

object ChooseEncoder {
  def apply(it: inlining.Trees)(using inox.Context): ChooseEncoder {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends ChooseEncoder(s, t)
    new Impl(it, it)
  }
}
