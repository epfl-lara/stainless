/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

trait ChainComparator { self: StructuralSize =>

  import checker.program._
  import checker.program.trees._
  import checker.program.symbols._
  import checker.program.trees.exprOps._

  def structuralDecreasing(e1: Expr, e2s: Seq[(Path, Expr)]): Seq[Expr] = flatTypesPowerset(e1.getType).toSeq.map {
    recons => andJoin(e2s.map { case (path, e2) =>
      path implies GreaterThan(self.fullSize(recons(e1)), self.fullSize(recons(e2)))
    })
  }
}

// vim: set ts=4 sw=4 et:
