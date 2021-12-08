/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

trait DefaultTactic extends Tactic {
  val description = "Default verification condition generation approach"

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  protected def getPostconditions(e: Expr, lambda: Lambda): Seq[Expr] = {
    def rec(e: Expr, path: Path): Seq[Expr] = e match {
      case NoTree(_) => Seq()
      case Let(i, e, b) => rec(b, path withBinding (i -> e))
      case Assert(cond, _, body) => rec(body, path withCond cond)
      case IfExpr(c, t, e) => rec(t, path withCond c) ++ rec(e, path withCond not(c))
      case MatchExpr(s, cases) =>
        var soFar = path
        (for (MatchCase(pattern, guard, rhs) <- cases) yield {
          val guardOrTrue = guard.getOrElse(BooleanLiteral(true))

          val patternPath = conditionForPattern[Path](s, pattern, includeBinders = true)
          val vcs = rec(rhs, soFar merge (patternPath withCond guardOrTrue))

          val patternPathNeg = conditionForPattern[Path](s, pattern, includeBinders = false)
          val guardMapped = exprOps.replaceFromSymbols(mapForPattern(s, pattern), guardOrTrue)
          soFar = soFar merge (patternPathNeg withCond guardMapped).negate
          vcs
        }).flatten

      case p: Passes =>
        Seq()

      case _ =>
        val Lambda(Seq(res), b @ TopLevelAnds(es)) = lambda
        val body = andJoin(es.filterNot {
          case Annotated(e, flags) => flags contains DropConjunct
          case p: Passes => true
          case _ => false
        }).copiedFrom(b)

        if (body != BooleanLiteral(true)) {
          Seq((path implies Let(res, e, body).copiedFrom(e)).setPos(e))
        } else {
          Seq()
        }
    }

    val Lambda(Seq(res), b @ TopLevelAnds(es)) = lambda
    val examples = es collect { case p: Passes => p.asConstraint }
    val examplesPost = if (examples.nonEmpty) Seq(Let(res, e, andJoin(examples)).copiedFrom(e)) else Seq()

    rec(e, Path.empty) ++ examplesPost
  }

  def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.postcondition, fd.body) match {
      case (Some(post @ Lambda(Seq(res), _)), Some(body)) if !res.flags.contains(DropVCs) =>
        getPostconditions(body, post).map { vc =>
          val vcKind = if (fd.flags.exists(_.name == "law")) VCKind.Law else VCKind.Postcondition
          VC(exprOps.freshenLocals(implies(fd.precOrTrue, vc)), id, vcKind, false).setPos(vc)
        }
      case _ => Nil
    }
  }

  protected def getPrecondition(pre: Expr): Option[Expr] = pre match {
    case TopLevelAnds(es) =>
      val pred = andJoin(es.filterNot {
        case Annotated(e, flags) => flags contains DropConjunct
        case _ => false
      }).copiedFrom(pre)

      if (pred != BooleanLiteral(true)) {
        Some(pred)
      } else {
        None
      }
  }

  def generatePreconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)

    val calls = collectForConditions {
      case (fi: FunctionInvocation, path) if fi.tfd.precondition.isDefined => (fi, path)
    }(fd.fullBody)

    calls.flatMap { case (fi @ FunctionInvocation(_, _, args), path) =>
      getPrecondition(fi.tfd.precondition.get).map { pred =>
        val pre = fi.tfd.withParamSubst(args, pred)
        val vc = path implies exprOps.freshenLocals(pre)
        val fiS = sizeLimit(fi.asString, 40)
        VC(vc, id, VCKind.Info(VCKind.Precondition, s"call $fiS"), false).setPos(fi)
      }
    }
  }

  // FIXME(gsps): Should also filter individual conjuncts?
  protected def annotatedAsUnchecked(e: Expr): Boolean = e match {
    case Annotated(_, flags) if flags.contains(DropConjunct) => true
    case _ => false
  }

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {
    // We don't collect preconditions here, because these are handled by generatePreconditions
    collectForConditions {
      case (m @ MatchExpr(scrut, cases), path) =>
        val condition = path implies orJoin(cases map (matchCaseCondition[Path](scrut, _).toClause))
        VC(condition, id, VCKind.ExhaustiveMatch, false).setPos(m)

      case (e @ Error(_, _), path) =>
        val condition = Not(path.toClause)
        VC(condition, id, VCKind.Assert, false).setPos(e)

      case (a @ Assert(cond, optErr, _), path) if !annotatedAsUnchecked(cond) =>
        val condition = path implies cond
        val kind = VCKind.fromErr(optErr)
        VC(condition, id, kind, false).setPos(a)

      case (c @ Choose(res, pred), path) if !(res.flags contains DropVCs) =>
        if (path.conditions.isEmpty && exprOps.variablesOf(c).isEmpty) {
          VC(pred, id, VCKind.Info(VCKind.Choose, "check-sat"), true).setPos(c)
        } else {
          val condition = path implies Not(Forall(Seq(res), Not(pred)))
          VC(condition, id, VCKind.Choose, false).setPos(c)
        }

      case (a @ ADT(aid, tps, args), path) if a.getConstructor.sort.hasInvariant =>
        val invId = a.getConstructor.sort.invariant.get.id
        val condition = path implies FunctionInvocation(invId, tps, Seq(a))
        VC(condition, id, VCKind.AdtInvariant(invId), false).setPos(a)
    }(getFunction(id).fullBody)
  }
}

object DefaultTactic {
  def apply(p: StainlessProgram, ctx: inox.Context): DefaultTactic { val program: p.type } = new DefaultTactic {
    val program: p.type = p
    val context = ctx
  }
}
