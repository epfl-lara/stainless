/* Copyright 2009-2026 EPFL, Lausanne */

import stainless.lang._

object OldInParamRefinement {
  case class Box(var x: BigInt)

  def f(b: { v: Box with v.x == old(v).x }): Unit = {
    b.x = b.x + 1
  }
}
