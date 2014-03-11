/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

trait RelationComparator { self : StructuralSize =>

  def sizeDecreasing(e1: Expr, e2: Expr) = GreaterThan(self.size(e1), self.size(e2))

  def softDecreasing(e1: Expr, e2: Expr) = GreaterEquals(self.size(e1), self.size(e2))
}

// vim: set ts=4 sw=4 et:
