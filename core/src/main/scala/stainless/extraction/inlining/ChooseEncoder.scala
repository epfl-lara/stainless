/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

/** Hides each `choose` under a fresh function of the variables in its scope, whose body is the `choose`. Unless the
  * `choose` is marked with `DropVCs`, its call asserts that its predicate is satisfiable.
  *
  * The `choose`s in the field types of sorts are hidden the same way. Since a type can't hold an assertion, their
  * satisfiability is checked in another fresh function, which asserts it for all the values of the variables in scope
  * (the earlier fields of the constructor and the binders of the enclosing refinements). That function is derived
  * from the invariant of the sort, if any, so that it is checked with it.
  */
class ChooseEncoder(override val s: ast.Trees, override val t: ast.Trees)
                   (using override val context: inox.Context)
  extends CachingPhase with NoSummaryPhase with SimplyCachedFunctions with SimplyCachedSorts { self =>

  type TransformerContext = s.Symbols
  override def getContext(symbols: s.Symbols) = symbols

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected type SortResult = (t.ADTSort, Seq[t.FunDef])
  override protected def registerSorts(symbols: t.Symbols, sorts: Seq[(t.ADTSort, Seq[t.FunDef])]): t.Symbols =
    symbols.withSorts(sorts.map(_._1)).withFunctions(sorts.flatMap(_._2))

  /** Lifts the `choose`s of a definition with type parameters `tparams`, at position `pos`. The `choose`s of function
    * bodies assert their satisfiability where they are called, and the others, when `satFlags` is defined, in a fresh
    * function with these flags.
    */
  private class ChooseLifter(tparams: Seq[s.TypeParameterDef], origin: Identifier, var pos: inox.utils.Position,
                             satFlags: Option[Seq[t.Flag]]) extends inox.transformers.Transformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    type Env = Seq[t.ValDef]

    import t._ // for implicit `VariableConverter`, required for `replaceFromSymbols`

    var chooses = Seq[t.FunDef]()
    private var inType = false

    private lazy val newTparams = tparams.map(transform(_, Seq()))

    override def transform(tpe: s.Type, env: Seq[t.ValDef]): t.Type = tpe match {
      case s.RefinementType(vd, pred) =>
        val newVd = transform(vd, env)
        val wasInType = inType
        inType = true
        try t.RefinementType(newVd, transform(pred, env :+ newVd)).copiedFrom(tpe)
        finally inType = wasInType

      case _ =>
        val wasInType = inType
        inType = true
        try super.transform(tpe, env)
        finally inType = wasInType
    }

    override def transform(e: s.Expr, env: Seq[t.ValDef]): t.Expr = e match {
      // the variables bound in scope have the types of their binders, whose `choose`s are already lifted
      case v: s.Variable if env.exists(_.id == v.id) =>
        env.findLast(_.id == v.id).get.toVariable.copiedFrom(v)

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

      case c @ s.Choose(vd, pred) =>
        val wasInType = inType
        inType = false
        // the choose's own type and predicate are in an expression, whatever encloses it
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
        inType = wasInType

        val newFd = new t.FunDef(
          FreshIdentifier("choose", true), newTparams, freshParams,
          returnType,
          newChoose,
          Seq(t.Derived(Some(origin)), t.DropVCs),
        ).setPos(pos)

        chooses = chooses :+ newFd

        val fi = t.FunctionInvocation(newFd.id, newFd.tparams.map(_.tp), env.map(_.toVariable)).copiedFrom(c)
        def satisfiable(pos: inox.utils.Position) =
          t.Not(t.Forall(Seq(transform(vd, env)), t.Not(transform(pred, env)).setPos(pos)).setPos(pos)).setPos(pos)
        if (vd.flags.contains(s.DropVCs))
          fi
        else if (!inType)
          t.Assert(satisfiable(c.getPos), Some("Choose satisfiability"), fi).setPos(c)
        else {
          for (flags <- satFlags) {
            // the positions of the trees in types may be lost
            val satPos = if (c.getPos == inox.utils.NoPosition) pos else c.getPos
            val (_, satParams) = freshParams.foldLeft((Map[t.ValDef, t.Expr](), Seq[t.ValDef]())) {
              case ((substMap, vds), vd) =>
                val nvd = t.ValDef(vd.id.freshen, t.typeOps.replaceFromSymbols(substMap, vd.tpe), vd.flags).copiedFrom(vd)
                (substMap + (vd -> nvd.toVariable), vds :+ nvd)
            }
            val satSubst = (env zip satParams.map(_.toVariable)).toMap[t.ValDef, t.Expr]
            chooses = chooses :+ new t.FunDef(
              FreshIdentifier("chooseSatisfiability", true), newTparams, satParams,
              t.UnitType(),
              t.Assert(exprOps.replaceFromSymbols(satSubst, satisfiable(satPos)), Some("Choose satisfiability"),
                t.UnitLiteral().setPos(satPos)).setPos(satPos),
              flags,
            ).setPos(satPos)
          }
          fi
        }

      case _ => super.transform(e, env)
    }
  }

  protected def extractFunction(context: TransformerContext, fd: s.FunDef): (Seq[t.FunDef], Unit) = {
    val lifter = new ChooseLifter(fd.tparams, fd.id, fd.getPos, Some(Seq(t.Derived(Some(fd.id)))))
    val params2 = fd.params.map(lifter.transform(_, Seq()))
    val newFd = new t.FunDef(
      fd.id,
      fd.tparams.map(lifter.transform(_, Seq())),
      params2,
      lifter.transform(fd.returnType, params2),
      lifter.transform(fd.fullBody, params2),
      fd.flags.map(lifter.transform(_, Seq()))
    ).setPos(fd)
    (lifter.chooses :+ newFd, ())
  }

  protected def extractSort(context: TransformerContext, sort: s.ADTSort): ((t.ADTSort, Seq[t.FunDef]), Unit) = {
    // the satisfiability of the chooses of a library sort is trusted, as are its other VCs
    val satFlags =
      if (sort.flags.exists(_.name == "library")) None
      else Some(Seq(t.Derived(sort.flags.collectFirst { case s.HasADTInvariant(id) => id })))
    val lifter = new ChooseLifter(sort.tparams, sort.id, sort.getPos, satFlags)
    val newSort = new t.ADTSort(
      sort.id,
      sort.tparams.map(lifter.transform(_, Seq())),
      sort.constructors.map { cons =>
        val fields = cons.fields.foldLeft(Seq[t.ValDef]()) { (fields, vd) =>
          for (p <- Seq(vd.getPos, cons.getPos, sort.getPos).find(_ != inox.utils.NoPosition)) lifter.pos = p
          fields :+ lifter.transform(vd, fields)
        }
        new t.ADTConstructor(cons.id, cons.sort, fields).copiedFrom(cons)
      },
      sort.flags.map(lifter.transform(_, Seq()))
    ).copiedFrom(sort)
    ((newSort, lifter.chooses), ())
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
