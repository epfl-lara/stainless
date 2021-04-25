/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.genc

trait NamedLeonPhase[-F, +T] extends LeonPipeline[F, T] {
  val underlying: LeonPipeline[F, T]
  val name: String

  private implicit val debugSection = DebugSectionGenC

  override def run(ctx: inox.Context, p: F): T = {
    ctx.reporter.debug("\n" * 2)
    ctx.reporter.debug("=" * 100)
    ctx.reporter.debug(s"Running phase $name on")
    ctx.reporter.debug(p)
    val res = ctx.timers.genc.get(name).run {
      underlying.run(ctx, p)
    }
    ctx.reporter.debug(s"Finished running phase $name")
    ctx.reporter.debug(res)
    ctx.reporter.debug("=" * 100)
    ctx.reporter.debug("\n" * 4)
    res
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
