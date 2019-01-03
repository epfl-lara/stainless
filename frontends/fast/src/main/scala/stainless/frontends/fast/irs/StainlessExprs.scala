package stainless.frontends.fast.irs

import stainless.frontends.fast.IRs

trait StainlessExprs extends inox.parser.irs.Exprs {self: IRs =>
  object StainlessExprs {

    abstract class StainelessExpr extends Exprs.Expr {
      override def getHoles: Seq[Hole] = this match {
        case a: Exprs.Expr => a.getHoles
        case _ => Seq()
      }
    }


    case class Int32Literal(value: Int) extends StainelessExpr with Exprs.Literal
    case class Int16Literal(value: Short) extends StainelessExpr with Exprs.Literal
    case class Int8Literal(value: Byte) extends StainelessExpr with Exprs.Literal

    object AdditionalOperators {
      case object Union extends Exprs.Binary.Operator
      case object Difference extends Exprs.Binary.Operator
      case object Contains extends Exprs.Binary.Operator
      case object IsDefinedAt extends Exprs.Binary.Operator
    }
  }
}
