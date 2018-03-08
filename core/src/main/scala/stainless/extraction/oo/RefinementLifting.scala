/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction.oo

import scala.collection.mutable.{Map => MutableMap}

trait RefinementLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    import s._
    import syms._

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

      case _ => None
    } (tpe)

    def dropRefinements(tpe: s.Type): s.Type = liftRefinements(tpe) match {
      case s.RefinementType(vd, _) => vd.tpe
      case _ => tpe
    }

    def parameterConds(vds: Seq[s.ValDef]): (Seq[s.ValDef], s.Expr) = {
      val (newParams, conds) = vds.map(vd => liftRefinements(vd.tpe) match {
        case s.RefinementType(vd2, pred) =>
          (
            vd.copy(tpe = vd2.tpe).copiedFrom(vd),
            s.exprOps.replaceFromSymbols(Map(vd2 -> vd.toVariable), pred)
          )
        case _ =>
          (vd, s.BooleanLiteral(true).copiedFrom(vd))
      }).unzip

      (newParams, s.andJoin(conds))
    }

    object transformer extends TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(vd: s.ValDef): t.ValDef =
        super.transform(vd.copy(tpe = dropRefinements(vd.tpe)).copiedFrom(vd))

      override def transform(e: s.Expr): t.Expr = e match {
        case s.IsInstanceOf(expr, tpe) => liftRefinements(tpe) match {
          case s.RefinementType(vd, pred) =>
            transform(s.and(
              s.IsInstanceOf(expr, vd.tpe).copiedFrom(e),
              s.exprOps.replaceFromSymbols(Map(vd -> s.AsInstanceOf(expr, vd.tpe).copiedFrom(e)), pred)
            ).copiedFrom(e))

          case _ => super.transform(e)
        }

        // Clean up for casts introduced during AdtSpecialization
        case s.AsInstanceOf(adt @ s.ADT(id, tps, es), s.RefinementType(vd, s.IsConstructor(v: Variable, cid)))
        if vd == v.toVal && id == cid =>
          transform(adt)

        case s.AsInstanceOf(expr, tpe) => liftRefinements(tpe) match {
          case s.RefinementType(vd, pred) =>
            transform(s.Assert(
              s.exprOps.replaceFromSymbols(Map(vd -> s.AsInstanceOf(expr, vd.tpe).copiedFrom(e)), pred),
              Some("Cast error"),
              s.AsInstanceOf(expr, vd.tpe).copiedFrom(e)
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

        case _ => super.transform(e)
      }

      override def transform(tpe: s.Type): t.Type = super.transform(liftRefinements(tpe))
    }

    val invariants: MutableMap[Identifier, s.FunDef] = MutableMap.empty

    val sorts: Seq[t.ADTSort] = syms.sorts.values.toList.map { sort =>
      val v = s.Variable.fresh("v", s.ADTType(sort.id, sort.typeArgs))
      val (newCons, conds) = sort.constructors.map { cons =>
        val (newFields, conds) = parameterConds(cons.fields)
        val newCons = cons.copy(fields = newFields).copiedFrom(cons)
        val newCond = s.implies(isCons(v, cons.id), conds)
        (newCons, newCond)
      }.unzip

      val cond = s.andJoin(conds).copiedFrom(sort)
      val optInv = if (cond == s.BooleanLiteral(true)) {
        None
      } else {
        val inv = sort.invariant match {
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
              case tparams => (
                Seq("thiss" :: s.ADTType(sort.id, tparams).copiedFrom(sort)),
                s.BooleanType().copiedFrom(sort), { case Seq(thiss) =>
                  s.typeOps.instantiateType(
                    s.exprOps.replaceFromSymbols(Map(v -> thiss), cond),
                    (sort.typeArgs zip tparams).toMap
                  )
                })
            }.copiedFrom(sort)
        }
        invariants(inv.id) = inv
        Some(inv.id)
      }

      transformer.transform(sort.copy(
        constructors = newCons,
        flags = sort.flags ++ optInv.map(s.HasADTInvariant(_))
      ).copiedFrom(sort))
    }

    // TODO: lift refinements to invariant?
    val classes: Seq[t.ClassDef] = syms.classes.values.toList.map(transformer.transform)

    val functions: Seq[t.FunDef] = syms.functions.values.toList.map { fd =>
      val withPre = if (invariants contains fd.id) {
        fd
      } else {
        val (newParams, conds) = parameterConds(fd.params)
        val optPre = s.andJoin(s.exprOps.preconditionOf(fd.fullBody).toSeq :+ conds) match {
          case s.BooleanLiteral(true) => None
          case cond => Some(cond)
        }

        fd.copy(
          fullBody = s.exprOps.withPrecondition(fd.fullBody, optPre),
          returnType = dropRefinements(fd.returnType)
        ).copiedFrom(fd)
      }

      transformer.transform(withPre)
    }

    val finalSyms = t.NoSymbols.withSorts(sorts).withClasses(classes).withFunctions(functions)

    for (fd <- finalSyms.functions.values) {
      if (!finalSyms.isSubtypeOf(fd.fullBody.getType(finalSyms), fd.returnType)) {
        println(fd)
        println(finalSyms.explainTyping(fd.fullBody)(t.PrinterOptions(printUniqueIds = true, symbols = Some(finalSyms))))
      }
    }

    finalSyms
  }
}
