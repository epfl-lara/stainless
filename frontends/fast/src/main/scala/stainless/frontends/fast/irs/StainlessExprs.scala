package stainless.frontends.fast.irs

import stainless.frontends.fast.IRs

trait StainlessExprs extends inox.parser.irs.Exprs {self: IRs =>
  object StainlessExprs {

    abstract class StainlessExpr extends Exprs.Expr {
      override def getHoles: Seq[Hole] = this match {
        case a: Require => a.contract.getHoles ++ a.body.getHoles
        case a: Exprs.Expr => a.getHoles
        case _ => Seq()
      }
    }

    case class Int32Literal(value: Int) extends StainlessExpr with Exprs.Literal
    case class Int16Literal(value: Short) extends StainlessExpr with Exprs.Literal
    case class Int8Literal(value: Byte) extends StainlessExpr with Exprs.Literal
    case class Int64Literal(value: Long) extends StainlessExpr with Exprs.Literal

    object AdditionalOperators {
      case object Union extends Exprs.Binary.Operator
      case object Difference extends Exprs.Binary.Operator
      case object Contains extends Exprs.Binary.Operator
      case object Updated extends Exprs.Binary.Operator
    }

    case class Require(contract: Exprs.Expr, body: Exprs.Expr) extends StainlessExpr
  }
}
