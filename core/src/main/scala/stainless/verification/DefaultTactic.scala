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
          VC(exprOps.freshenLocals(implies(fd.precOrTrue, vc)), id, VCKind.Postcondition).setPos(fd)
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
      VC(vc, id, VCKind.Info(VCKind.Precondition, s"call $fiS")).setPos(fi)
    }
  }

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {

    def eToVCKind(e: Expr) = e match {
      case _ : MatchExpr =>
        VCKind.ExhaustiveMatch

      case Assert(_, Some(err), _) =>
        if (err.startsWith("Array ")) {
          VCKind.ArrayUsage
        } else if (err.startsWith("Map ")) {
          VCKind.MapUsage
        } else if (err.endsWith("Overflow")) {
          VCKind.Overflow
        } else if (err.startsWith("Shift")) {
          VCKind.Shift
        } else if (err.startsWith("Division ")) {
          VCKind.DivisionByZero
        } else if (err.startsWith("Modulo ")) {
          VCKind.ModuloByZero
        } else if (err.startsWith("Remainder ")) {
          VCKind.RemainderByZero
        } else if (err.startsWith("Cast ")) {
          VCKind.CastError
        } else {
          VCKind.AssertErr(err)
        }

      case _: Choose =>
        VCKind.Choose

      case _: ADT =>
        VCKind.AdtInvariant

      case _ =>
        VCKind.Assert
    }

    // We don't collect preconditions here, because these are handled by generatePreconditions
    val calls = collectForConditions {
      case (m @ MatchExpr(scrut, cases), path) =>
        (m, path implies orJoin(cases map (matchCaseCondition[Path](scrut, _).toClause)))

      case (e @ Error(_, _), path) =>
        (e, Not(path.toClause))

      case (a @ Assert(cond, _, _), path) =>
        (a, path implies cond)

      case (c @ Choose(res, pred), path) if !(res.flags contains Unchecked) =>
        (c, path implies Not(Forall(Seq(res), Not(pred))))

      case (a @ ADT(id, tps, args), path) if a.getConstructor.sort.hasInvariant =>
        (a, path implies FunctionInvocation(a.getConstructor.sort.invariant.get.id, tps, Seq(a)))
    }(getFunction(id).fullBody)

    calls.map { case (e, correctnessCond) =>
      VC(correctnessCond, id, eToVCKind(e)).setPos(e)
    }
  }
}

object DefaultTactic {
  def apply(p: StainlessProgram, ctx: inox.Context): DefaultTactic { val program: p.type } = new DefaultTactic {
    val program: p.type = p
    val context = ctx
  }
}
