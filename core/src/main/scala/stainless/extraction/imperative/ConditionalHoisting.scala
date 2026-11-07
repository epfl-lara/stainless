/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

class ConditionalHoisting(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.SimplePhase
     with SimplyCachedFunctions
     with IdentitySorts
     with oo.SimplyCachedClasses
     with oo.SimplyCachedTypeDefs { self =>
  import s._

  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {

    object hoister extends ConcreteOOSelfTreeTransformer {
      private case class Hoisted(bindings: Seq[(ValDef, Expr)], expr: Expr) {
        def map(f: Expr => Expr): Hoisted = copy(expr = f(expr))

        def wrapped: Expr = bindings.foldRight(expr) { case ((vd, value), body) =>
          Let(vd, value, body).copiedFrom(value)
        }
      }

      override def transform(e: Expr): Expr = e match {
        case Let(vd, value, body) => hoist(value).map(Let(vd, _, transform(body)).copiedFrom(e)).wrapped
        case LetVar(vd, value, body) => hoist(value).map(LetVar(vd, _, transform(body)).copiedFrom(e)).wrapped
        case Block(statements, last) => transformBlock(statements, last)
        case _: IfExpr | _: MatchExpr | _: Assignment => hoist(e).wrapped
        case _ => super.transform(e)
      }

      private def transformBlock(statements: Seq[Expr], last: Expr): Expr = statements match {
        case Seq() => transform(last)
        case statement +: rest => hoist(statement).map(prepend(_, transformBlock(rest, last))).wrapped
      }

      private def prepend(statement: Expr, rest: Expr): Expr = rest match {
        case Block(statements, last) => Block(statement +: statements, last).copiedFrom(statement)
        case _ => Block(Seq(statement), rest).copiedFrom(statement)
      }

      private def hoist(e: Expr): Hoisted = e match {
        case e: IfExpr => hoistCondition(e)
        case e: MatchExpr => lowerMatch(e)
        case Assignment(v, value) => hoist(value).map(Assignment(v, _).copiedFrom(e))
        case _ => Hoisted(Seq.empty, transform(e))
      }

      private def hoistCondition(e: IfExpr): Hoisted = {
        val cond = ValDef.fresh("cond", BooleanType()).copiedFrom(e.cond)
        val ifExpr = IfExpr(cond.toVariable, transform(e.thenn), transform(e.elze)).copiedFrom(e)
        Hoisted(Seq(cond -> transform(e.cond)), ifExpr)
      }

      private def lowerMatch(e: MatchExpr): Hoisted = {
        val (scrutineeBindings, scrutinee) = bindScrutinee(transform(e.scrutinee))
        val matches = e.cases.map(matchCase => ValDef.fresh("matches", BooleanType()).copiedFrom(matchCase))

        val conditions = e.cases.indices.map { i =>
          val previousFailed = matches.take(i).map(previous => Not(previous.toVariable).copiedFrom(previous))
          and(previousFailed :+ caseCondition(scrutinee, e.cases(i))*)
        }

        val exhaustivenessError: Expr = Error(e.getType, "match exhaustiveness").copiedFrom(e)
        val ifChain = matches.zip(e.cases).foldRight(exhaustivenessError) { case ((matched, matchCase), elze) =>
          IfExpr(matched.toVariable, caseBody(scrutinee, matchCase), elze).copiedFrom(matchCase)
        }

        Hoisted(scrutineeBindings ++ matches.zip(conditions), ifChain)
      }

      private def bindScrutinee(scrutinee: Expr): (Seq[(ValDef, Expr)], Variable) = scrutinee match {
        case v: Variable => (Seq.empty, v)
        case _ =>
          val scrut = ValDef.fresh("scrut", scrutinee.getType).copiedFrom(scrutinee)
          (Seq(scrut -> scrutinee), scrut.toVariable)
      }

      private def caseCondition(scrutinee: Variable, matchCase: MatchCase): Expr = {
        val patternTest = symbols.conditionForPattern[Path](scrutinee, matchCase.pattern).toClause
        matchCase.optGuard match {
          case Some(guard) => and(patternTest, exprOps.freshenLocals(bindBinders(scrutinee, matchCase.pattern, transform(guard))))
          case None => patternTest
        }
      }

      private def caseBody(scrutinee: Variable, matchCase: MatchCase): Expr =
        bindBinders(scrutinee, matchCase.pattern, transform(matchCase.rhs))

      private def bindBinders(scrutinee: Variable, pattern: Pattern, body: Expr): Expr = {
        val bindings = symbols.mapForPattern(scrutinee, pattern)
        bindings.foldRight(body) { case ((binder, value), rest) =>
          Let(binder, value, rest).copiedFrom(body)
        }
      }
    }

    override def transform(fd: s.FunDef): t.FunDef = {
      val (specs, bodyOpt) = exprOps.deconstructSpecs(fd.fullBody)
      val hoistedBody = bodyOpt.map(hoister.transform)
      val hoistedFullBody = exprOps.reconstructSpecs(specs, hoistedBody, fd.returnType)

      super.transform(fd.copy(fullBody = hoistedFullBody).copiedFrom(fd))
    }
  }

  override protected def getContext(syms: s.Symbols) = new TransformerContext(self.s, self.t)(using syms)
}

object ConditionalHoisting extends ExtractionPipelineCreator {
  override val name: String = "ConditionalHoisting"

  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ConditionalHoisting(s)(t)
    new Impl(trees, trees)
  }
}
