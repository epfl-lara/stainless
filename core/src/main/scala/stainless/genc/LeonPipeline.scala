/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package genc

abstract class LeonPipeline[-F, +T] {
  self =>

  def andThen[G](thenn: LeonPipeline[T, G]): LeonPipeline[F, G] = new LeonPipeline[F,G] {
    def run(ctx: inox.Context, v: F): G = {
      // if(ctx.findOptionOrDefault(GlobalOptions.optStrictPhases)) ctx.reporter.terminateIfError()
      thenn.run(ctx, self.run(ctx, v))
    }
  }

  def when[F2 <: F, T2 >: T](cond: Boolean)(implicit tps: F2 =:= T2): LeonPipeline[F2, T2] = {
    if (cond) this else new LeonPipeline[F2, T2] {
      def run(ctx: inox.Context, v: F2): T2 = v
    }
  }

  def run(ctx: inox.Context, v: F): T
}

object LeonPipeline {

  def both[T, R1, R2](f1: LeonPipeline[T, R1], f2: LeonPipeline[T, R2]): LeonPipeline[T, (R1, R2)] = new LeonPipeline[T, (R1, R2)] {
    def run(ctx: inox.Context, t: T): (R1, R2) = {
      val r1 = f1.run(ctx, t)
      // don't check for SharedOptions.optStrictPhases because f2 does not depend on the result of f1
      val r2 = f2.run(ctx, t)
      (r1, r2)
    }
  }

}
