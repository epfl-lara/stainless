/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._

trait RelationComparator { self : StructuralSize =>

  def sizeDecreasing(e1: Expr, e2: Expr) = GreaterThan(self.size(e1), self.size(e2))

  def softDecreasing(e1: Expr, e2: Expr) = GreaterEquals(self.size(e1), self.size(e2))
}

// vim: set ts=4 sw=4 et:
