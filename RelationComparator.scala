/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

class RelationComparator(structuralSize: StructuralSize) {
  import structuralSize.size

  def sizeDecreasing(e1: Expr, e2: Expr) = GreaterThan(size(e1), size(e2))

  def softDecreasing(e1: Expr, e2: Expr) = GreaterEquals(size(e1), size(e2))
}

// vim: set ts=4 sw=4 et:
