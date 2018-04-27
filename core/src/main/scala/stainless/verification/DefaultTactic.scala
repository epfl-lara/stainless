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

      case _ => Seq((path implies application(lambda, Seq(e))).setPos(e))
    }

    rec(e, Path.empty)
  }

  def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        getPostconditions(body, post).map { vc =>
          VC(exprOps.freshenLocals(implies(fd.precOrTrue, vc)), id, VCKind.Postcondition, false).setPos(fd)
        }
      case _ => Nil
    }
  }

  def generatePreconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)

    val calls = collectForConditions {
      case (fi: FunctionInvocation, path) if fi.tfd.precondition.isDefined => (fi, path)
    }(fd.fullBody)

    calls.map { case (fi @ FunctionInvocation(_, _, args), path) =>
      val pre = fi.tfd.withParamSubst(args, fi.tfd.precondition.get)
      val vc = path implies exprOps.freshenLocals(pre)
      val fiS = sizeLimit(fi.asString, 40)
      VC(vc, id, VCKind.Info(VCKind.Precondition, s"call $fiS"), false).setPos(fi)
    }
  }

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)

    // We don't collect preconditions here, because these are handled by generatePreconditions
    val bodyVCs = collectForConditions {
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
        val condition = path implies FunctionInvocation(a.getConstructor.sort.invariant.get.id, tps, Seq(a))
        VC(condition, id, VCKind.AdtInvariant, false).setPos(a)
    }(fd.fullBody)

    val invariantSat = sorts.values.find(_.invariant.exists(_.id == id)).map { sort =>
      val v = Variable.fresh("s", ADTType(sort.id, sort.typeArgs))
      val condition = FunctionInvocation(id, sort.typeArgs, Seq(v))
      VC(condition, id, VCKind.InvariantSat, true).setPos(sort)
    }

    bodyVCs ++ invariantSat
  }
}

object DefaultTactic {
  def apply(p: StainlessProgram, ctx: inox.Context): DefaultTactic { val program: p.type } = new DefaultTactic {
    val program: p.type = p
    val context = ctx
  }
}
