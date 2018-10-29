/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

trait DefaultTactic extends Tactic {
  val description = "Default verification condition generation approach"

  import context._
  import program._
  import program.trees._
  import program.symbols._

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

      case _ =>
        val Lambda(Seq(res), b @ TopLevelAnds(es)) = lambda
        val body = andJoin(es.filterNot {
          case Annotated(e, flags) => flags contains Unchecked
          case _ => false
        }).copiedFrom(b)

        if (body != BooleanLiteral(true)) {
          Seq((path implies Let(res, e, body).copiedFrom(e)).setPos(e))
        } else {
          Seq()
        }
    }

    rec(e, Path.empty)
  }

  def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.postcondition, fd.body) match {
      case (Some(post @ Lambda(Seq(res), _)), Some(body)) if !res.flags.contains(Unchecked) =>
        getPostconditions(body, post).map { vc =>
          val vcKind = if (fd.flags.exists(_.name == "law")) VCKind.Law else VCKind.Postcondition
          VC(exprOps.freshenLocals(implies(fd.precOrTrue, vc)), id, vcKind, false).setPos(fd)
        }
      case _ => Nil
    }
  }

  protected def getPrecondition(pre: Expr): Option[Expr] = pre match {
    case TopLevelAnds(es) =>
      val pred = andJoin(es.filterNot {
        case Annotated(e, flags) => flags contains Unchecked
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

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {
    // We don't collect preconditions here, because these are handled by generatePreconditions
    collectForConditions {
      case (m @ MatchExpr(scrut, cases), path) =>
        val condition = path implies orJoin(cases map (matchCaseCondition[Path](scrut, _).toClause))
        VC(condition, id, VCKind.ExhaustiveMatch, false).setPos(m)

      case (e @ Error(_, _), path) =>
        val condition = Not(path.toClause)
        VC(condition, id, VCKind.Assert, false).setPos(e)

      case (a @ Assert(cond, optErr, _), path) =>
        val condition = path implies cond
        val kind = optErr.map { err =>
          if (err.startsWith("Array ")) VCKind.ArrayUsage
          else if (err.startsWith("Map ")) VCKind.MapUsage
          else if (err.endsWith("Overflow")) VCKind.Overflow
          else if (err.startsWith("Shift")) VCKind.Shift
          else if (err.startsWith("Division ")) VCKind.DivisionByZero
          else if (err.startsWith("Modulo ")) VCKind.ModuloByZero
          else if (err.startsWith("Remainder ")) VCKind.RemainderByZero
          else if (err.startsWith("Cast ")) VCKind.CastError
          else VCKind.AssertErr(err)
        }.getOrElse(VCKind.Assert)
        VC(condition, id, kind, false).setPos(a)

      case (c @ Choose(res, pred), path) if !(res.flags contains Unchecked) =>
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
