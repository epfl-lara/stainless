/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package genc

abstract class LeonPipeline[F, T](val context: inox.Context) { self =>

  def andThen[G](thenn: LeonPipeline[T, G]): LeonPipeline[F, G] =
    new LeonPipeline[F,G](self.context) {
      def run(v: F): G = {
        thenn.run(self.run(v))
      }
    }

  def run(v: F): T
}

object LeonPipeline {

  def both[T, R1, R2](f1: LeonPipeline[T, R1], f2: LeonPipeline[T, R2])(using ctx: inox.Context): LeonPipeline[T, (R1, R2)] =
    new LeonPipeline[T, (R1, R2)](ctx) {
      def run(t: T): (R1, R2) = {
        val r1 = f1.run(t)
        // don't check for SharedOptions.optStrictPhases because f2 does not depend on the result of f1
        val r2 = f2.run(t)
        (r1, r2)
      }
    }

}
