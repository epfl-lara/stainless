/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.genc

trait NamedLeonPhase[-F, +T] extends LeonPipeline[F, T] {
  val underlying: LeonPipeline[F, T]
  val name: String

  override def run(ctx: inox.Context, p: F) = {
    ctx.timers.genc.get(name).run {
      underlying.run(ctx, p)
    }
  }
}

object NamedLeonPhase {
  def apply[F, T](s: String, pipeline: LeonPipeline[F, T]): LeonPipeline[F, T] {
  } = new {
    override val underlying: pipeline.type = pipeline
    override val name: String = s
  } with NamedLeonPhase[F, T]
}

abstract class UnitPhase[T] extends LeonPipeline[T, T] {
  def apply(ctx: inox.Context, p: T): Unit

  override def run(ctx: inox.Context, p: T) = {
    apply(ctx, p)
    p
  }
}

case class NoopPhase[T]() extends LeonPipeline[T, T] {
  override def run(ctx: inox.Context, v: T) = v
}
