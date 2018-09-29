/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package utils

object DebugSectionTrees extends inox.DebugSection("trees")

trait DebugPipeline extends ExtractionPipeline with PositionChecker { self =>
  val name: String
  val underlying: ExtractionPipeline
  override val s: underlying.s.type = underlying.s
  override val t: underlying.t.type = underlying.t
  override val context = underlying.context

  private[this] val phases = context.options.findOption(optDebugPhases)
  private[this] val objects = context.options.findOption(optDebugObjects).getOrElse(Seq()).toSet

  // We print debug output for this phase only if the user didn't specify
  // any phase with --debug-phases, or gave the name of (or a string
  // contained in) this phase
  private[this] val debug = phases.isEmpty || phases.exists(_ contains name)

  // Moreover, we only print when the corresponding debug sections are active
  private[this] val debugTrees: Boolean = debug && context.reporter.debugSections.contains(DebugSectionTrees)
  private[this] val debugPos: Boolean = debug && context.reporter.debugSections.contains(DebugSectionPositions)

  private[this] val tPrinterOpts = t.PrinterOptions.fromContext(context)

  private[this] val positions = new PositionTraverser

  override def invalidate(id: Identifier) = underlying.invalidate(id)

  // `extract` is a wrapper around `super.extract` which outputs trees for
  // debugging and which outputs position checks
  override def extract(symbols: s.Symbols): t.Symbols = {
    implicit val debugSection = DebugSectionTrees

    val symbolsToPrint = if (debugTrees) symbols.debugString(objects)(printerOpts) else ""
    if (!symbolsToPrint.isEmpty) {
      context.reporter.debug("\n\n\n\nSymbols before " + name + "\n")
      context.reporter.debug(symbolsToPrint)
    }

    // extraction happens here
    val res = context.timers.extraction.get(name).run(underlying.extract(symbols))

    val resToPrint = if (debugTrees) res.debugString(objects)(tPrinterOpts) else ""
    if (!symbolsToPrint.isEmpty || !resToPrint.isEmpty) {
      context.reporter.debug("\n\nSymbols after " + name +  "\n")
      context.reporter.debug(resToPrint)
      context.reporter.debug("\n\n")
    }

    if (debugPos) {
      res.functions.values foreach(positions.traverse)
    }

    res
  }
}

object DebugPipeline {
  def apply(nme: String, pipeline: ExtractionPipeline): ExtractionPipeline {
    val s: pipeline.s.type
    val t: pipeline.t.type
  } = new {
    override val underlying: pipeline.type = pipeline
    override val name: String = nme
  } with DebugPipeline
}
