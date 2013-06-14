package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

object RelationComparator {
  import StructuralSize._

  def init : Unit = StructuralSize.init

  def sizeDecreasing(e1: TypedExpr, e2: TypedExpr) = GreaterThan(size(e1), size(e2))
  def sizeDecreasing(e1:      Expr, e2: TypedExpr) = GreaterThan(size(e1), size(e2))
  def sizeDecreasing(e1: TypedExpr, e2:      Expr) = GreaterThan(size(e1), size(e2))
  def sizeDecreasing(e1:      Expr, e2:      Expr) = GreaterThan(size(e1), size(e2))

  def softDecreasing(e1: TypedExpr, e2: TypedExpr) = GreaterEquals(size(e1), size(e2))
  def softDecreasing(e1:      Expr, e2: TypedExpr) = GreaterEquals(size(e1), size(e2))
  def softDecreasing(e1: TypedExpr, e2:      Expr) = GreaterEquals(size(e1), size(e2))
  def softDecreasing(e1:      Expr, e2:      Expr) = GreaterEquals(size(e1), size(e2))
}

// vim: set ts=4 sw=4 et:
