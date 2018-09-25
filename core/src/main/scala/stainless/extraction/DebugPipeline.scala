/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

trait DebugPipeline extends ExtractionPipeline { self =>
  val name: String
  val underlying: ExtractionPipeline
  override val s: underlying.s.type = underlying.s
  override val t: underlying.t.type = underlying.t
  override val context = underlying.context

  implicit val debugSection = inox.ast.DebugSectionTrees
  val phases = context.options.findOption(optDebugPhases)
  val objs = context.options.findOption(optDebugObjects).getOrElse(Seq()).toSet

  // We print debug output for this phase only if the user didn't specify
  // any phase with --debug-phases, or gave the name of (or a string
  // contained in) this phase
  lazy val debug = phases.isEmpty || (phases.isDefined && phases.get.exists(name.contains _))

  // Moreover, we only print when the corresponding debug sections are active
  lazy val debugTrees: Boolean = debug && context.reporter.debugSections.contains(inox.ast.DebugSectionTrees)

  val ooPrinterOpts = oo.trees.PrinterOptions.fromContext(context)

  override def invalidate(id: Identifier) = underlying.invalidate(id)

  def objectsToString(tt: ast.Trees)(m: Iterable[(Identifier, tt.Definition)], pOpts: tt.PrinterOptions): String = 
    m.collect {
      case (id,d) if objs.isEmpty || objs.contains(id.name) =>
        d.asString(pOpts)
    }.mkString("\n\n")

  // make a String representation for a table of Symbols `s`, only keeping
  // functions and classes whose names appear in `objs`
  def symbolsToString(tt: ast.Trees)(syms: tt.Symbols, objs: Set[String], pOpts: tt.PrinterOptions): String = {

    val functions = objectsToString(tt)(syms.functions, pOpts) 
    val sorts = objectsToString(tt)(syms.sorts, pOpts)
    val classes =
      if (tt.isInstanceOf[oo.Trees])
        objectsToString(oo.trees)(syms.asInstanceOf[oo.trees.Symbols].classes, ooPrinterOpts)
      else
        ""

    def wrapWith(header: String, s: String) = {
      if (s.isEmpty) ""
      else
        "-------------" + header + "-------------\n" +
        s + "\n\n"
    }

    wrapWith("Functions", functions) ++
    wrapWith("Sorts", sorts) ++
    wrapWith("Classes", classes)
  }

  // `extract` is a wrapper around `super.extract` which outputs trees for
  // debugging and which outputs position checks
  override def extract(symbols: s.Symbols): t.Symbols = {
    context.reporter.synchronized {
      val symbolsToPrint = if (debugTrees) symbolsToString(s)(symbols, objs, printerOpts) else ""
      if (!symbolsToPrint.isEmpty) {
        context.reporter.debug("\n\n\n\nSymbols before " + name + "\n")
        context.reporter.debug(symbolsToPrint)
      }

      // extraction happens here
      val res = context.timers.extraction.get(name).run(underlying.extract(symbols))
      val resToPrint = if (debugTrees) symbolsToString(t)(res, objs, targetPrinterOpts) else ""

      if (!symbolsToPrint.isEmpty || !resToPrint.isEmpty) {
        context.reporter.debug("\n\nSymbols after " + name +  "\n")
        context.reporter.debug(resToPrint)
        context.reporter.debug("\n\n")
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
