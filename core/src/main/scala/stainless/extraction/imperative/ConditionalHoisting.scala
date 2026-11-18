/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Turns the matches of mutable type into `if` chains, and binds to fresh variables the conditions of `if`s that are neither immutable nor class tests of variables that keep their object, so that branches start from a known heap. */
class ConditionalHoisting(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.SimplePhase
     with SimplyCachedFunctions
     with IdentitySorts
     with oo.SimplyCachedClasses
     with oo.SimplyCachedTypeDefs { self =>
  import s._

  override protected def getContext(syms: s.Symbols) = new TransformerContext(self.s, self.t)(using syms)

  /** Hoists the bodies and the specifications of the functions of `symbols`. */
  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {

    override def transform(fd: s.FunDef): t.FunDef = {
      val (specs, bodyOpt) = exprOps.deconstructSpecs(fd.fullBody)
      val hoistedSpecs = specs.map(_.transform(e => new Hoister().transform(e)))
      val hoistedBody = bodyOpt.map(new Hoister().transform)
      val hoistedFullBody = exprOps.reconstructSpecs(hoistedSpecs, hoistedBody, fd.returnType)

      super.transform(fd.copy(fullBody = hoistedFullBody).copiedFrom(fd))
    }

    /** Hoists the conditions and scrutinees out of the expressions of mutable type. */
    class Hoister extends ConcreteOOSelfTreeTransformer {
      /** `expr`, to run after the hoisted `bindings`. */
      private case class Hoisted(bindings: Seq[(ValDef, Expr)], expr: Expr) {
        /** The same bindings, with `f` applied to the expression. */
        def map(f: Expr => Expr): Hoisted = copy(expr = f(expr))

        /** The expression under its bindings. */
        def toExpr: Expr = bindings.foldRight(expr) { case ((vd, value), body) =>
          Let(vd, value, body).copiedFrom(value)
        }
      }

      override def transform(e: Expr): Expr = e match {
        case Let(vd, value, body) => hoist(value).map(Let(vd, _, transform(body)).copiedFrom(e)).toExpr
        case LetVar(vd, value, body) => hoist(value).map(LetVar(vd, _, transform(body)).copiedFrom(e)).toExpr
        case Block(statements, last) => transformBlock(statements, last)
        case _: IfExpr | _: MatchExpr | _: Assignment => hoist(e).toExpr
        case _ => super.transform(e)
      }

      /** The block of `statements` and `last`, each statement after its own hoisted bindings. */
      private def transformBlock(statements: Seq[Expr], last: Expr): Expr = {
        def prepend(statement: Expr, rest: Expr): Expr = rest match {
          case Block(restStatements, restLast) => Block(statement +: restStatements, restLast).copiedFrom(statement)
          case _ => Block(Seq(statement), rest).copiedFrom(statement)
        }

        statements match {
          case Seq() => transform(last)
          case statement +: rest => hoist(statement).map(prepend(_, transformBlock(rest, last))).toExpr
        }
      }

      /** `e`, with the conditions and scrutinees it starts with hoisted. */
      private def hoist(e: Expr): Hoisted = e match {
        case e @ (_: IfExpr | _: MatchExpr) if !symbols.containsMutableType(e) => Hoisted(Seq.empty, super.transform(e))
        case e: IfExpr => hoistIf(e)
        case e: MatchExpr => hoistMatch(e)
        case Assignment(v, value) => hoist(value).map(Assignment(v, _).copiedFrom(e))
        case _ => Hoisted(Seq.empty, transform(e))
      }

      /** Whether `e` only tests the class of variables that keep their object. */
      private def isClassTest(e: Expr): Boolean = e match {
        case IsInstanceOf(v: Variable, _) => !v.flags.contains(IsVar)
        case IsConstructor(v: Variable, _) => !v.flags.contains(IsVar)
        case Not(inner) => isClassTest(inner)
        case And(exprs) => exprs.forall(isClassTest)
        case Or(exprs) => exprs.forall(isClassTest)
        case _ => false
      }

      /** The `if` `e`, its condition bound to a fresh variable unless it is immutable or a class test. */
      private def hoistIf(e: IfExpr): Hoisted = {
        if (symbols.isImmutableExpression(e.cond) || isClassTest(e.cond)) {
          return Hoisted(Seq.empty, IfExpr(transform(e.cond), transform(e.thenn), transform(e.elze)).copiedFrom(e))
        }

        val cond = ValDef.fresh("cond", BooleanType()).copiedFrom(e.cond)
        val ifExpr = IfExpr(cond.toVariable, transform(e.thenn), transform(e.elze)).copiedFrom(e)

        Hoisted(Seq(cond -> transform(e.cond)), ifExpr)
      }

      /** The match `e` as an `if` chain over its cases, its scrutinee bound to a fresh variable unless it is one. */
      private def hoistMatch(e: MatchExpr): Hoisted = {
        def bindScrutinee(scrutinee: Expr): (Seq[(ValDef, Expr)], Variable) = scrutinee match {
          case v: Variable => (Seq.empty, v)
          case _ =>
            val scrut = ValDef.fresh("scrut", scrutinee.getType).copiedFrom(scrutinee)

            (Seq(scrut -> scrutinee), scrut.toVariable)
        }

        def bindPatternBinders(scrutinee: Variable, matchCase: MatchCase, body: Expr): Expr = {
          val bindings = symbols.mapForPattern(scrutinee, matchCase.pattern)
          bindings.values.foreach(exprOps.preTraversal(_.ensurePos(matchCase.getPos)))

          bindings.foldRight(body) { case ((binder, value), rest) =>
            Let(binder, value, rest).copiedFrom(body)
          }
        }

        def caseCondition(scrutinee: Variable, matchCase: MatchCase): Expr = {
          val patternTest = exprOps.freshenLocals(symbols.conditionForPattern[Path](scrutinee, matchCase.pattern).toClause)

          matchCase.optGuard match {
            case Some(guard) =>
              val boundGuard = bindPatternBinders(scrutinee, matchCase, guard)

              and(patternTest, exprOps.freshenLocals(boundGuard))
            case None =>
              patternTest
          }
        }

        val (scrutineeBindings, scrutinee) = bindScrutinee(transform(e.scrutinee))

        val exhaustivenessError: Expr = Error(e.getType, "match exhaustiveness").copiedFrom(e)
        val ifChain = e.cases.foldRight(exhaustivenessError) { (matchCase, elze) =>
          val body = bindPatternBinders(scrutinee, matchCase, matchCase.rhs)

          IfExpr(caseCondition(scrutinee, matchCase), body, elze).copiedFrom(matchCase)
        }

        val hoistedChain = hoist(ifChain)

        Hoisted(scrutineeBindings ++ hoistedChain.bindings, hoistedChain.expr)
      }
    }
  }
}

object ConditionalHoisting extends ExtractionPipelineCreator {
  override val name: String = "ConditionalHoisting"

  /** The phase over the trees `trees`. */
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ConditionalHoisting(s)(t)

    new Impl(trees, trees)
  }
}
