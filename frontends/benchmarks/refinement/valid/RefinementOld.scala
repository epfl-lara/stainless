/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._

object RefinementOld {
  case class Box(var x: BigInt) {
    def bump(): {res: Boolean with old(this).x + 1 == this.x} = {
      x = x + 1
      true
    }
  }

  // `old` on a mutated parameter, in the refinement of the return type
  def addX(b: Box, y: BigInt): { res: Unit with b.x == old(b).x + y } = {
    b.x = b.x + y
  }

  // Same postcondition, written with `ensuring`
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

  // `old` on an immutable, unmutated parameter: old(t) == t
  case class Imm(i: BigInt)
  def immOld(t: Imm): { res: BigInt with res == old(t).i } = {
    t.i
  }
  
  def callerImm(): Unit = {
    val t = Imm(10)
    val temp = immOld(t)
    assert(immOld(t) == BigInt(10))
  }
  
}
