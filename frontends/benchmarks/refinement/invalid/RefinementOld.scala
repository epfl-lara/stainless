/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._

object RefinementOld {
  case class Box(var x: BigInt) {
    // The postcondition is wrong: it should be old(this).x + 1
    def bumpWrong(): {res: Boolean with old(this).x == this.x} = {
      x = x + 1
      true
    }
  }

  // The postcondition is wrong: it should be old(b).x + y
  def addX(b: Box, y: BigInt): { res: Unit with b.x == old(b).x } = {
    b.x = b.x + y
  }
}
