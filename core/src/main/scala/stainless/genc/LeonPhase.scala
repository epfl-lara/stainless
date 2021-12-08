/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.genc

import stainless.extraction.utils._

class NamedLeonPhase[F, T](val name: String,
                           val underlying: LeonPipeline[F, T])
                          (using context: inox.Context) extends LeonPipeline[F, T](context) {
  lazy val phases = context.options.findOption(optDebugPhases).map(_.toSet)

  lazy val debugTrees: Boolean =
    (phases.isEmpty || phases.exists(_.contains(name))) &&
    context.reporter.debugSections.contains(DebugSectionTrees)

  lazy val debugSizes: Boolean =
    (phases.isEmpty || phases.exists(_.contains(name))) &&
    context.reporter.debugSections.contains(DebugSectionSizes)

  private given givenDebugSection: DebugSectionTrees.type = DebugSectionTrees

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
        case prog: ir.IRs.SIR.Prog => prog.size
        case prog: ir.IRs.CIR.Prog => prog.size
        case prog: ir.IRs.RIR.Prog => prog.size
        case prog: ir.IRs.NIR.Prog => prog.size
        case prog: ir.IRs.LIR.Prog => prog.size
        case prog: CAST.Tree => prog.size
        case _ => 0
      }
      context.reporter.debug(s"Total number of lines after phase $name: $lines")(using DebugSectionSizes)
      context.reporter.debug(s"Total number of AST nodes after phase $name: $size")(using DebugSectionSizes)
    }
    res
  }
}

abstract class UnitPhase[T](context: inox.Context) extends LeonPipeline[T, T](context) {
  def apply(p: T): Unit

  override def run(p: T) = {
    apply(p)
    p
  }
}

object NoopPhase {
  def apply[T](using ctx: inox.Context): LeonPipeline[T, T] =
    new LeonPipeline[T, T](ctx) {
      override def run(v: T) = v
    }
}
