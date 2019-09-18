/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait RefinementLifting
  extends CachingPhase
     with SimpleFunctions
     with IdentityTypeDefs
     with SimpleClasses
     with SimplyCachedFunctions
     with SimplyCachedSorts
     with SimplyCachedClasses { self =>

  val s: Trees
  val t: Trees

  override protected type SortResult = (t.ADTSort, Option[t.FunDef])
  override protected def registerSorts(symbols: t.Symbols, sorts: Seq[(t.ADTSort, Option[t.FunDef])]): t.Symbols =
    symbols.withSorts(sorts.map(_._1)).withFunctions(sorts.flatMap(_._2))

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
    import s._
    import symbols._

    def liftRefinements(tpe: s.Type): s.Type = s.typeOps.postMap {
      case ft @ s.FunctionType(from, to) =>
        val nfrom = from.map { case s.RefinementType(vd, pred) => vd.tpe case tpe => tpe }
        to match {
          case s.RefinementType(vd, pred) =>
            val nvd = s.ValDef(FreshIdentifier("f"), s.FunctionType(nfrom, vd.tpe).copiedFrom(ft), vd.flags).copiedFrom(vd)
            val args = from.map(tpe => s.ValDef(FreshIdentifier("x"), tpe).copiedFrom(pred))
            val app = s.Application(nvd.toVariable, args.map(_.toVariable)).copiedFrom(pred)
            val npred = s.Forall(args, s.exprOps.replaceFromSymbols(Map(vd -> app), pred)).copiedFrom(pred)
            Some(s.RefinementType(nvd, npred).copiedFrom(pred))
          case _ =>
            Some(s.FunctionType(nfrom, to).copiedFrom(ft))
        }

      case s.TupleType(tps) =>
        val (ctps, optPreds) = tps.map {
          case s.RefinementType(vd, pred) => (vd.tpe, Some(vd -> pred))
          case tpe => (tpe, None)
        }.unzip

        if (optPreds.forall(_.isEmpty)) None else {
          val nvd = s.ValDef(FreshIdentifier("t"), s.TupleType(ctps).copiedFrom(tpe)).copiedFrom(tpe)
          val npred = s.andJoin(optPreds.zipWithIndex.flatMap {
            case (Some((vd, pred)), i) =>
              Some(s.exprOps.replaceFromSymbols(Map(vd -> s.TupleSelect(nvd.toVariable, i + 1).copiedFrom(vd)), pred))
            case _ => None
          })
          Some(s.RefinementType(nvd, npred).copiedFrom(tpe))
        }

      case ta: s.TypeApply if !ta.isAbstract =>
        Some(ta.resolve)

      case _ => None
    } (tpe)

    def dropRefinements(tpe: s.Type): s.Type = liftRefinements(tpe) match {
      case s.RefinementType(vd, _) => dropRefinements(vd.tpe)
      case _ => tpe
    }

    def parameterConds(vds: Seq[s.ValDef]): (Seq[s.ValDef], s.Expr) = {
      val (newParams, conds) = vds.map(vd => liftRefinements(vd.tpe) match {
        case s.RefinementType(vd2, pred) =>
          val (Seq(nvd), pred2) = parameterConds(Seq(vd.copy(tpe = vd2.tpe).copiedFrom(vd)))

          (nvd, s.exprOps.replaceFromSymbols(Map(vd2 -> nvd.toVariable), s.and(pred, pred2)))
        case _ =>
          (vd, s.BooleanLiteral(true).copiedFrom(vd))
      }).unzip

      (newParams, s.andJoin(conds))
    }

    override def transform(vd: s.ValDef): t.ValDef =
      super.transform(vd.copy(tpe = dropRefinements(vd.tpe)).copiedFrom(vd))

    override def transform(e: s.Expr): t.Expr = e match {
      case s.IsInstanceOf(expr, tpe) => liftRefinements(tpe) match {
        case s.RefinementType(vd, pred) =>
          transform(s.and(
            isInstOf(expr, vd.tpe).copiedFrom(e),
            s.exprOps.replaceFromSymbols(Map(vd -> asInstOf(expr, vd.tpe).copiedFrom(e)), pred)
          ).copiedFrom(e))

        case _ => super.transform(e)
      }

      case s.AsInstanceOf(expr, tpe) => liftRefinements(tpe) match {
        case s.RefinementType(vd, s.BooleanLiteral(true)) =>
          transform(asInstOf(expr, vd.tpe).copiedFrom(e))

        case s.RefinementType(vd, pred) =>
          transform(s.Assert(
            s.exprOps.freshenLocals(s.exprOps.replaceFromSymbols(Map(vd -> asInstOf(expr, vd.tpe).copiedFrom(e)), pred)),
            Some("Cast error"),
            asInstOf(expr, vd.tpe).copiedFrom(e)
          ).copiedFrom(e))

        case _ => super.transform(e)
      }

      case s.ApplyLetRec(id, tparams, tpe, tps, args) => liftRefinements(tpe) match {
        case s.RefinementType(vd, s.BooleanLiteral(true)) =>
          val ftTpe = vd.tpe.asInstanceOf[s.FunctionType]
          transform(s.ApplyLetRec(id, tparams, ftTpe, tps, args))

        case s.RefinementType(vd, pred) =>
          val params = args.zipWithIndex.map { case (arg, i) => s.ValDef.fresh(s"i$i", arg.getType) }
          val subst = Map(
            vd -> s.Lambda(
              params,
              s.ApplyLetRec(id, tparams, vd.tpe.asInstanceOf[s.FunctionType], tps, params.map(_.toVariable))
            )
          )
          transform(s.Assert(
            s.exprOps.freshenLocals(s.exprOps.replaceFromSymbols(subst, pred)),
            Some("Inner refinement lifting"),
            s.ApplyLetRec(id, tparams, vd.tpe.asInstanceOf[s.FunctionType], tps, args)
          ).copiedFrom(e))

        case _ => super.transform(e)
      }

      case s.Choose(res, pred) =>
        val (Seq(nres), cond) = parameterConds(Seq(res))
        t.Choose(transform(nres), t.and(transform(cond), transform(pred)).copiedFrom(e)).copiedFrom(e)

      case s.Forall(args, pred) =>
        val (nargs, cond) = parameterConds(args)
        t.Forall(nargs map transform, t.implies(transform(cond), transform(pred)).copiedFrom(e)).copiedFrom(e)

      case s.Lambda(args, body) =>
        val (nargs, cond) = parameterConds(args)
        t.Lambda(nargs map transform, t.assume(transform(cond), transform(body)).copiedFrom(e)).copiedFrom(e)

      case s.MatchExpr(scrut, cses) =>
        t.MatchExpr(transform(scrut), cses.map { case cse @ s.MatchCase(pat, guard, rhs) =>
          var conds: Seq[s.Expr] = Seq.empty
          val newPat = s.patternOps.postMap {
            case pat @ s.InstanceOfPattern(ob, tpe) => liftRefinements(tpe) match {
              case s.RefinementType(vd, pred) =>
                val binder = ob.getOrElse(vd)
                conds :+= s.exprOps.replaceFromSymbols(Map(vd -> binder.toVariable), pred)
                Some(s.InstanceOfPattern(Some(binder), vd.tpe).copiedFrom(pat))
              case _ => None
            }

            case _ => None
          } (pat)

          val optGuard = s.andJoin(conds ++ guard) match {
            case s.BooleanLiteral(true) => None
            case cond => Some(cond)
          }

          t.MatchCase(transform(newPat), optGuard map transform, transform(rhs)).copiedFrom(cse)
        }).copiedFrom(e)

      case _ =>
        super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = super.transform(liftRefinements(tpe))
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    import s._

    val (newParams, cond) = context.parameterConds(fd.params)
    val optPre = cond match {
      case cond if cond != s.BooleanLiteral(true) => s.exprOps.preconditionOf(fd.fullBody) match {
        case Some(pre) => Some(s.and(cond, pre).copiedFrom(pre))
        case None => Some(cond.copiedFrom(fd))
      }
      case _ => s.exprOps.preconditionOf(fd.fullBody)
    }

    val optPost = context.liftRefinements(fd.returnType) match {
      case s.RefinementType(vd2, pred) => s.exprOps.postconditionOf(fd.fullBody) match {
        case Some(post @ s.Lambda(Seq(res), body)) =>
          Some(s.Lambda(Seq(res), s.and(
              exprOps.replaceFromSymbols(Map(vd2 -> res.toVariable), pred),
              body).copiedFrom(body)).copiedFrom(post))
        case None =>
          Some(s.Lambda(Seq(vd2), pred).copiedFrom(fd))
      }
      case _ => s.exprOps.postconditionOf(fd.fullBody)
    }

    context.transform(fd.copy(
      fullBody = s.exprOps.withPostcondition(s.exprOps.withPrecondition(fd.fullBody, optPre), optPost),
      returnType = context.dropRefinements(fd.returnType)
    ).copiedFrom(fd))
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): (t.ADTSort, Option[t.FunDef]) = {
    import s._
    import context.symbols._

    val v = s.Variable.fresh("v", s.ADTType(sort.id, sort.typeArgs))
    val (newCons, conds) = sort.constructors.map { cons =>
      val (newFields, conds) = context.parameterConds(cons.fields)
      val newCons = cons.copy(fields = newFields).copiedFrom(cons)
      val newCond = s.implies(
        isCons(v, cons.id).copiedFrom(cons),
        s.exprOps.replaceFromSymbols(
          newFields.map(vd => vd.toVariable -> s.ADTSelector(v, vd.id).copiedFrom(cons)).toMap,
          conds
        )
      ).copiedFrom(cons)
      (newCons, newCond)
    }.unzip

    val cond = s.andJoin(conds).copiedFrom(sort)
    val optInv = if (cond == s.BooleanLiteral(true)) {
      None
    } else {
      Some(sort.invariant match {
        case Some(fd) =>
          fd.copy(fullBody = s.and(
            s.typeOps.instantiateType(
              s.exprOps.replaceFromSymbols(Map(v -> fd.params.head.toVariable), cond),
              (sort.typeArgs zip fd.typeArgs).toMap
            ),
            fd.fullBody
          ).copiedFrom(fd.fullBody)).copiedFrom(fd)

        case None =>
          import s.dsl._
          mkFunDef(FreshIdentifier("inv"))(sort.typeArgs.map(_.id.name) : _*) {
            tparams => (
              Seq("thiss" :: s.ADTType(sort.id, tparams).copiedFrom(sort)),
              s.BooleanType().copiedFrom(sort), { case Seq(thiss) =>
                s.typeOps.instantiateType(
                  s.exprOps.replaceFromSymbols(Map(v -> thiss), cond),
                  (sort.typeArgs zip tparams).toMap
                )
              })
          }.copiedFrom(sort)
      })
    }

    val newSort = context.transform(sort.copy(
      constructors = newCons,
      flags = sort.flags ++ optInv.map(fd => s.HasADTInvariant(fd.id))
    ).copiedFrom(sort))

    val newInv = optInv.map(fd => context.transform(fd))

    (newSort, newInv)
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = {
    // TODO: lift refinements to invariant?
    context.transform(cd)
  }
}

object RefinementLifting {
  def apply(ts: Trees, tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new RefinementLifting {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
