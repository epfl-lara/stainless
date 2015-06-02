/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import leon.purescala.Constructors._

trait RelationComparator { self : StructuralSize =>

  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterThan(self.size(tupleWrap(args1)), self.size(tupleWrap(args2)))
  }

  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterEquals(self.size(tupleWrap(args1)), self.size(tupleWrap(args2)))
  }

}

// vim: set ts=4 sw=4 et:
