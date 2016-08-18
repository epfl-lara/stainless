/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait ExprOps extends inox.ast.ExprOps {
  protected val trees: Trees
  import trees._

  protected class VariableExtractor extends super.VariableExtractor {
    override def unapply(e: Expr): Option[(Set[Variable], Set[Variable])] = e match {
      case MatchExpr(_, cases) => Some((Set.empty, cases.flatMap(_.pattern.binders).map(_.toVariable).toSet))
      case _ => super.unapply(e)
    }
  }

  override val VariableExtractor = new VariableExtractor
}
