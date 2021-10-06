/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.genc

import stainless.extraction.utils._

trait NamedLeonPhase[F, T] extends LeonPipeline[F, T] {
  val underlying: LeonPipeline[F, T]
  val name: String

  lazy val phases = context.options.findOption(optDebugPhases).map(_.toSet)

  lazy val debugTrees: Boolean =
    (phases.isEmpty || phases.exists(_.contains(name))) &&
    context.reporter.debugSections.contains(DebugSectionTrees)

  lazy val debugSizes: Boolean =
    (phases.isEmpty || phases.exists(_.contains(name))) &&
    context.reporter.debugSections.contains(DebugSectionSizes)

  private implicit val debugSection = DebugSectionTrees

  override def run(p: F): T = {
    if (debugTrees) {
      context.reporter.debug("\n" * 2)
      context.reporter.debug("=" * 100)
      context.reporter.debug(s"Running phase $name on:\n")
      context.reporter.debug(p)
    }
    val res = context.timers.genc.get(name).run {
      underlying.run(p)
    }
    if (debugTrees) {
      context.reporter.debug("\n")
      context.reporter.debug("-" * 100)
      context.reporter.debug(s"Finished running phase $name:\n")
      context.reporter.debug(res)
      context.reporter.debug("=" * 100)
      context.reporter.debug("\n" * 4)
    }
    if (debugSizes) {
      val lines = res.toString.count(_ == '\n') + 1
      val size = res match {
        case symbols: stainless.extraction.throwing.trees.Symbols => symbols.astSize
        case prog: ir.IRs.SIR.Prog => prog.size(context)
        case prog: ir.IRs.CIR.Prog => prog.size(context)
        case prog: ir.IRs.RIR.Prog => prog.size(context)
        case prog: ir.IRs.NIR.Prog => prog.size(context)
        case prog: ir.IRs.LIR.Prog => prog.size(context)
        case prog: CAST.Tree => prog.size(context)
        case _ => 0
      }
      context.reporter.debug(s"Total number of lines after phase $name: $lines")(DebugSectionSizes)
      context.reporter.debug(s"Total number of AST nodes after phase $name: $size")(DebugSectionSizes)
    }
    res
  }
}

object NamedLeonPhase {

  def apply[F, T](s: String, pipeline: LeonPipeline[F, T])(implicit ctx: inox.Context): LeonPipeline[F, T] {
  } = new {
    override val underlying: pipeline.type = pipeline
    override val name: String = s
    override val context = ctx
  } with NamedLeonPhase[F, T]
}

trait UnitPhase[T] extends LeonPipeline[T, T] {
  def apply(p: T): Unit

  override def run(p: T) = {
    apply(p)
    p
  }
}

object NoopPhase {
  def apply[T](implicit ctx: inox.Context): LeonPipeline[T, T] = {
    new {
      override val context = ctx
    } with LeonPipeline[T, T] {
      override def run(v: T) = v
    }
  }
}
