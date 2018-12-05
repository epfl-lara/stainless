package stainless.frontends.fast.elaborators

import scala.util.parsing.input.Position

trait ExprElaborators extends inox.parser.elaboration.elaborators.ExprElaborators { self: stainless.frontends.fast.Elaborators =>

  class StainlessExprE extends super.ExprE {

    override def elaborate(template: Exprs.Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
      case PatternMatchings.MatchExpression(lhs, cases) =>
        for {
          (_, eventualLhs) <- ExprE.elaborate(lhs)
          (tpe, cases) <- MatchCaseSeqE.elaborate(cases)
        } yield (tpe, Eventual.withUnifier {implicit unifier =>
          trees.MatchExpr(eventualLhs.get, cases.get)
        })
      case _ => super.elaborate(template)
    }
  }

  override val ExprE = new StainlessExprE

  class OptExprE extends Elaborator[Either[Position, Exprs.Expr], (SimpleTypes.Type, Eventual[trees.Expr])] {
    override def elaborate(optExpr: Either[Position, Exprs.Expr])(implicit store: Store):
    Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = optExpr match {
      case Right(expr) =>
        ExprE.elaborate(expr)
      case Left(pos) => {
        Constrained.pure((SimpleTypes.BooleanType().setPos(pos), Eventual.pure(trees.BooleanLiteral(true))))
      }
    }
  }
  val OptExprE = new OptExprE
}
