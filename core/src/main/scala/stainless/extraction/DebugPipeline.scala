/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

trait DebugPipeline extends ExtractionPipeline with utils.PositionChecker { self =>
  val name: String
  val underlying: ExtractionPipeline
  override val s: underlying.s.type = underlying.s
  override val t: underlying.t.type = underlying.t
  override val context = underlying.context

  private[this] val phases = context.options.findOption(optDebugPhases)
  private[this] val objs = context.options.findOption(optDebugObjects).getOrElse(Seq()).toSet

  // We print debug output for this phase only if the user didn't specify
  // any phase with --debug-phases, or gave the name of (or a string
  // contained in) this phase
  private[this] val debug = phases.isEmpty || (phases.isDefined && phases.get.exists(name.contains _))

  // Moreover, we only print when the corresponding debug sections are active
  private[this] val debugTrees: Boolean = debug && context.reporter.debugSections.contains(inox.ast.DebugSectionTrees)
  private[this] val debugPos: Boolean = debug && context.reporter.debugSections.contains(utils.DebugSectionPositions)

  val ooPrinterOpts = oo.trees.PrinterOptions.fromContext(context)

  override def invalidate(id: Identifier) = underlying.invalidate(id)

  // `extract` is a wrapper around `super.extract` which outputs trees for
  // debugging and which outputs position checks
  override def extract(symbols: s.Symbols): t.Symbols = {
    implicit val debugSection = inox.ast.DebugSectionTrees

    context.reporter.synchronized {
      val symbolsToPrint = if (debugTrees) symbols.debugString(objs)(printerOpts) else ""
      if (!symbolsToPrint.isEmpty) {
        context.reporter.debug("\n\n\n\nSymbols before " + name + "\n")
        context.reporter.debug(symbolsToPrint)
      }

      // extraction happens here
      val res = context.timers.extraction.get(name).run(underlying.extract(symbols))
      val resToPrint = if (debugTrees) res.debugString(objs)(targetPrinterOpts) else ""

      if (!symbolsToPrint.isEmpty || !resToPrint.isEmpty) {
        context.reporter.debug("\n\nSymbols after " + name +  "\n")
        context.reporter.debug(resToPrint)
        context.reporter.debug("\n\n")
      }

      if (debugPos) {
        res.functions.values foreach { fd =>
          (new PositionTraverser).traverse(fd)
        }
      }

      res
    }
  }
}

object DebugPipeline {
  def apply(nme: String, pipeline: ExtractionPipeline): ExtractionPipeline {
    val s: pipeline.s.type
    val t: pipeline.t.type
  } = new {
    override val underlying: pipeline.type = pipeline
  } with DebugPipeline {
    override val name: String = nme
  }
}
