/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

/** Hides each `choose` of a function body under a fresh function of the variables in its scope, whose body is the
  * `choose`. Unless the `choose` is marked with `DropVCs`, its call asserts that its predicate is satisfiable.
  *
  * A `choose` in a type (as in the refinement of a field, a parameter or a result) is rejected: a type can't assert
  * the satisfiability of its predicate. It can be moved into a function that the type calls.
  */
class ChooseEncoder(override val s: ast.Trees, override val t: ast.Trees)
                   (using override val context: inox.Context)
  extends CachingPhase with NoSummaryPhase with SimplyCachedFunctions with SimpleSorts with SimplyCachedSorts { self =>

  type TransformerContext = s.Symbols
  override def getContext(symbols: s.Symbols) = symbols

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  private def rejectChoose(c: s.Choose, defn: s.Definition): Nothing =
    context.reporter.fatalError(if (c.getPos == inox.utils.NoPosition) defn.getPos else c.getPos,
      s"`choose` is not supported in the types of ${defn.id.asString}, since types can't check that its predicate " +
      "is satisfiable: move it into a function and call that function instead")

  private class IdentitySortsImpl(override val s: self.s.type, override val t: self.t.type)
    extends stainless.transformers.ConcreteTreeTransformer(s, t)
  private val identity = new IdentitySortsImpl(self.s, self.t)

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): (t.ADTSort, Unit) = {
    for (cons <- sort.constructors; vd <- cons.fields) {
      s.typeOps.preTraversal {
        case s.RefinementType(_, pred) => s.exprOps.preTraversal {
          case c: s.Choose => rejectChoose(c, sort)
          case _ =>
        } (pred)
        case _ =>
      } (vd.tpe)
    }
    (identity.transform(sort), ())
  }

  protected def extractFunction(context: TransformerContext, fd: s.FunDef): (Seq[t.FunDef], Unit) = {
    var fdChooses = Seq[t.FunDef]()

    object ce extends inox.transformers.Transformer {
      override val s: self.s.type = self.s
      override val t: self.t.type = self.t

      type Env = Seq[t.ValDef]

      import t._ // for implicit `VariableConverter`, required for `replaceFromSymbols`

      private var inType = false

      override def transform(tpe: s.Type, env: Seq[t.ValDef]): t.Type = {
        val wasInType = inType
        inType = true
        try super.transform(tpe, env)
        finally inType = wasInType
      }

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

        case s.Forall(params, body) =>
          val (newParams, newEnv) = params.foldLeft((Seq[t.ValDef](), env)) {
            case ((accParams, accEnv), vd) =>
              val newVd = transform(vd, accEnv)
              (accParams :+ newVd, accEnv :+ newVd)
          }
          t.Forall(newParams, transform(body, newEnv)).copiedFrom(e)

        case c: s.Choose if inType => rejectChoose(c, fd)

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
    (fdChooses :+ newFd, ())
  }

}

object ChooseEncoder {
  def apply(st: ast.Trees, tt: ast.Trees)(using inox.Context): ChooseEncoder {
    val s: st.type
    val t: tt.type
  } = {
    class Impl(override val s: st.type, override val t: tt.type) extends ChooseEncoder(s, t)
    new Impl(st, tt)
  }
}
