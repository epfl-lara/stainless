/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

trait InductionTactic extends DefaultTactic {
  override val description = "Induction tactic for suitable functions"

  import context._
  import program._
  import program.trees._
  import program.symbols._

  private def firstSort(args: Seq[ValDef]): Option[(TypedADTSort, ValDef)] = {
    args.map(vd => (vd.getType, vd)).collect {
      case (adt: ADTType, vd) if adt.getSort.definition.isInductive => (adt.getSort, vd)
    }.headOption
  }

  private def selectorsOfParentType(tsort: TypedADTSort, tcons: TypedADTConstructor, expr: Expr): Seq[Expr] = {
    val tpe = ADTType(tsort.id, tsort.tps)
    val childrenOfSameType = tcons.fields.collect { case vd if vd.tpe == tpe => vd }
    for (field <- childrenOfSameType) yield adtSelector(expr, field.id)
  }

  private def inductOn(fd: FunDef): Option[(TypedADTSort, ValDef)] = {
    val flag = fd.flags collectFirst { case i: Induct => i }
    flag match {
      case Some(Induct(Some(on))) =>
        val param = fd.params find (_.id.name == on)
        param match {
          case Some(vd) =>
            firstSort(Seq(vd))
          case None =>
            reporter.error(fd.getPos, s"Could not find parameter named '$on' to induct on")
            None
        }
      case _ => firstSort(fd.params)
    }
  }

  override def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.body, inductOn(fd), fd.postcondition) match {
      case (Some(body), Some((tsort, arg)), Some(post)) =>
        (for (tcons <- tsort.constructors) yield {
          val selectors = selectorsOfParentType(tsort, tcons, arg.toVariable)

          val subCases = selectors.map { sel =>
            exprOps.replace(Map(arg.toVariable -> sel), implies(fd.precOrTrue, application(post, Seq(body))))
          }

          val kind = VCKind.Info(VCKind.Postcondition, s"ind. on ${arg.asString} / ${tcons.id.asString}")
          getPostconditions(body, post).map { vc =>
            val inductiveVC = exprOps.freshenLocals(implies(
              and(IsConstructor(arg.toVariable, tcons.id), fd.precOrTrue),
              implies(andJoin(subCases), vc)
            ))

            VC(inductiveVC, id, kind, false).setPos(fd)
          }
        }).flatten

      case (body, _, post) =>
        if (post.isDefined && body.isDefined) {
          reporter.warning(fd.getPos, "Could not find abstract class type argument to induct on")
        }
        super.generatePostconditions(id)
    }
  }

  override def generatePreconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.body, firstSort(fd.params)) match {
      case (Some(b), Some((tsort, arg))) =>
        val body = b

        val calls = collectForConditions {
          case (fi: FunctionInvocation, path) if fi.tfd.hasPrecondition => (fi, path)
        }(body)

        (for {
          (fi @ FunctionInvocation(_, _, args), path) <- calls
          pre = fi.tfd.precondition.get
          tcons <- tsort.constructors
        } yield {
          val selectors = selectorsOfParentType(tsort, tcons, arg.toVariable)

          val subCases = selectors.map { sel =>
            exprOps.replace(Map(arg.toVariable -> sel),
              exprOps.freshenLocals(path.implies(fi.tfd.withParamSubst(args, pre)))
            )
          }

          getPrecondition(pre).map { pred =>
            val vc = exprOps.freshenLocals(path
              .withConds(Seq(IsConstructor(arg.toVariable, tcons.id), fd.precOrTrue) ++ subCases)
              .implies(fi.tfd.withParamSubst(args, pred)))

            // Crop the call to display it properly
            val fiS = sizeLimit(fi.asString, 25)
            val kind = VCKind.Info(VCKind.Precondition, s"call $fiS, ind. on (${arg.asString} : ${tcons.id.asString})")
            VC(vc, id, kind, false).setPos(fi)
          }
        }).flatten

      case (body, _) =>
        if (body.isDefined) {
          reporter.warning(fd.getPos, "Could not find abstract class type argument to induct on")
        }
        super.generatePreconditions(id)
    }
  }
}

object InductionTactic {
  def apply(p: StainlessProgram, ctx: inox.Context): InductionTactic { val program: p.type } = new InductionTactic {
    val program: p.type = p
    val context = ctx
  }
}
