/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._

object OldInValRefinement {
  case class Box(var x: BigInt)

  def f(b: Box): Unit = {
    b.x = b.x + 1
    val y: { v: BigInt with v == old(b).x } = b.x
    ()
  }
}
