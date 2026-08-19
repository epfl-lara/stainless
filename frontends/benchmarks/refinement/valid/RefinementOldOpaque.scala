/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object RefinementOld {
  case class Box(var x: BigInt) {
    def bump(): {res: Boolean with old(this).x + 1 == this.x} = {
      x = x + 1
      true
    }
  }

  // `old` on a mutated parameter, in the refinement of the return type
  // it should work even if the function is opaque, since the postcondition is still visible to the caller
  @opaque 
  def addX(b: Box, y: BigInt): { res: Unit with b.x == old(b).x + y } = {
    b.x = b.x + y
  }

  // Same postcondition, written with `ensuring`
  @opaque 
  def addXEnsuring(b: Box, y: BigInt): Unit = {
    b.x = b.x + y
  }.ensuring(_ => b.x == old(b).x + y)

  // Callers can use the postcondition, in both styles
  def caller(): Unit = {
    val b = Box(10)
    addX(b, 5)
    assert(b.x == 15)
    addXEnsuring(b, 5)
    assert(b.x == 20)
  }
  
}
