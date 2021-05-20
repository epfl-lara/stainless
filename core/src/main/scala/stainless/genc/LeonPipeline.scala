/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package genc

abstract class LeonPipeline[F, T] { self =>

  val context: inox.Context

  def andThen[G](thenn: LeonPipeline[T, G]): LeonPipeline[F, G] = new {
    val context = self.context
  } with LeonPipeline[F,G] {
    def run(v: F): G = {
      thenn.run(self.run(v))
    }
  }

  def run(v: F): T
}

object LeonPipeline {

  def both[T, R1, R2](f1: LeonPipeline[T, R1], f2: LeonPipeline[T, R2])(implicit ctx: inox.Context): LeonPipeline[T, (R1, R2)] = new {
    val context = ctx
  } with LeonPipeline[T, (R1, R2)] {
    def run(t: T): (R1, R2) = {
      val r1 = f1.run(t)
      // don't check for SharedOptions.optStrictPhases because f2 does not depend on the result of f1
      val r2 = f2.run(t)
      (r1, r2)
    }
  }

}
