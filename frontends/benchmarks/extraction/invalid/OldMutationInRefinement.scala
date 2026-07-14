/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._

object OldMutationInRefinement {
  case class Box(var x: BigInt) {
    def bump(): Boolean = {
      x = x + 1
      true
    }
  }

  // The refinement predicate mutates the old state
  def f(b: Box): { res: Unit with old(b).bump() } = {
    b.x = 0
  }
}
