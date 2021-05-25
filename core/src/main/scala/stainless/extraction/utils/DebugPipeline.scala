/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package utils

object DebugSectionTrees extends inox.DebugSection("trees")

object optDebugObjects extends inox.OptionDef[Seq[String]] {
  val name = "debug-objects"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "o1,o2,..."
}

object optDebugPhases extends inox.OptionDef[Seq[String]] {
  import inox.OptionParsers._

  val name = "debug-phases"
  val default = Seq[String]()
  val parser: OptionParser[Seq[String]] = { s =>
    seqParser(stringParser)(s).filter(_.forall(phaseNames contains _))
  }

  val usageRhs = "p1,p2,..."
}

trait DebugSymbols extends PositionChecker { self =>
  val s: ast.Trees
  val t: ast.Trees

  val name: String
  val context: inox.Context

  private[this] lazy val positions = new PositionTraverser

  lazy val phases = context.options.findOption(optDebugPhases).map(_.toSet)
  lazy val objects = context.options.findOption(optDebugObjects)

  def filterObjects(name: String): Boolean = {
    objects.isEmpty || objects.exists(_.exists(r => name matches r))
  }

  // We print debug output for this phase only if the user didn't specify
  // any phase with --debug-phases, or gave the name of this phase
  lazy val isEnabled = phases.isEmpty || phases.exists(_.contains(name))

  // Moreover, we only print when the corresponding debug sections are active
  lazy val debugTrees: Boolean = isEnabled && context.reporter.debugSections.contains(DebugSectionTrees)
  lazy val debugPos: Boolean   = isEnabled && context.reporter.debugSections.contains(DebugSectionPositions)

  def debug[A](run: s.Symbols => t.Symbols)(symbols: s.Symbols): t.Symbols = {
    implicit val debugSection = DebugSectionTrees
    val sPrinterOpts = s.PrinterOptions.fromSymbols(symbols, context)
    val symbolsToPrint = if (debugTrees) symbols.debugString(filterObjects)(sPrinterOpts) else ""

    if (!symbolsToPrint.isEmpty) {
      context.reporter.debug(s"\n\n\n\nSymbols before $name\n")
      context.reporter.debug(symbolsToPrint)
    }

    val res = run(symbols)
    val tPrinterOpts = t.PrinterOptions.fromSymbols(res, context)

    val resToPrint = if (debugTrees) res.debugString(filterObjects)(tPrinterOpts) else ""
    if (!symbolsToPrint.isEmpty || !resToPrint.isEmpty) {
      if (resToPrint != symbolsToPrint) {
        context.reporter.debug(s"\n\nSymbols after $name\n")
        context.reporter.debug(resToPrint)
        context.reporter.debug("\n\n")
      } else {
        context.reporter.debug(s"Not printing symbols after $name as they did not change\n\n")
      }
    }

    if (debugTrees) {
      // ensure well-formedness after each extraction step
      context.reporter.debug(s"Ensuring well-formedness after phase $name...")
      try {
        res.ensureWellFormed
      } catch {
        case e: res.TypeErrorException =>
          context.reporter.debug(e)(frontend.DebugSectionStack)
          context.reporter.error(e.pos, e.getMessage)
          context.reporter.fatalError(s"Well-formedness check failed after phase $name")
        case e @ xlang.trees.NotWellFormedException(defn, _) =>
          context.reporter.debug(e)(frontend.DebugSectionStack)
          context.reporter.error(defn.getPos, e.getMessage)
          context.reporter.fatalError(s"Well-formedness check failed after phase $name")
      }
      context.reporter.debug(s"=> SUCCESS")
      context.reporter.debug(s"")
    }

    if (debugPos) {
      res.functions.values foreach(positions.traverse)
    }

    res
  }

  import inox.transformers.ProgramEncoder
  private type Encoder = ProgramEncoder {
    val sourceProgram: Program {
      val trees: self.s.type
    }
    val t: self.t.type
  }

  def debugEncoder(encoder: Encoder) = {
    debug(_ => encoder.targetProgram.symbols)(encoder.sourceProgram.symbols)
  }
}

trait DebugPipeline extends ExtractionPipeline with DebugSymbols { self =>
  val name: String
  val underlying: ExtractionPipeline

  override val s: underlying.s.type = underlying.s
  override val t: underlying.t.type = underlying.t
  override val context = underlying.context

  override def invalidate(id: Identifier) = underlying.invalidate(id)

  // `extract` is a wrapper around `super.extract` which outputs trees for
  // debugging and which outputs position checks
  override def extract(symbols: s.Symbols): t.Symbols = debug { syms =>
    context.timers.extraction.get(name).run(underlying.extract(syms))
  } (symbols)
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
