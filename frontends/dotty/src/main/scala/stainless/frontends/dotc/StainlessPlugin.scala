package stainless
package frontends.dotc

import dotty.tools.dotc
import dotc._
import core._
import Decorators.toMessage
import dotc.util._
import Contexts.{Context => DottyContext}
import plugins._
import Phases._
import Symbols._
import transform._
import reporting._
import inox.{Context, DebugSection, utils => InoxPosition}
import stainless.frontend
import stainless.frontend.{CallBack, Frontend}
import Utils._

object StainlessPlugin {
  val PluginName                       = "stainless"
  val PluginDescription                = "Inject Stainless verification pipeline"
  val EnableVerificationOptionName     = "verify:"
  val EnableGhostEliminationOptionName = "ghost-elim:"
}

case class PluginOptions(enableVerification: Boolean, enableGhostElimination: Boolean)

class StainlessPlugin extends StandardPlugin {
  import StainlessPlugin._

  override val name: String = PluginName
  override val description: String = PluginDescription

  def init(options: List[String]): List[PluginPhase] = {
    val pluginOpts = parseOptions(options)
    List(
      if (pluginOpts.enableVerification)
        Some(new ExtractionAndVerification)
      else None,
      if (pluginOpts.enableGhostElimination)
        Some(new GhostAccessRewriter(if (pluginOpts.enableVerification) "stainless" else Pickler.name))
      else None
    ).flatten
  }

  private def parseOptions(options: List[String]): PluginOptions = {
    var enableVerification = false
    var enableGhostElimination = false
    for (option <- options) {
      if (option.startsWith(EnableVerificationOptionName)) {
        val value = option.substring(EnableVerificationOptionName.length)
        parseBoolean(value) foreach { value =>
          enableVerification = value
        }
      }
      else if (option.startsWith(EnableGhostEliminationOptionName)) {
        val value = option.substring(EnableGhostEliminationOptionName.length)
        parseBoolean(value) foreach { value =>
          enableGhostElimination = value
        }
      }
    }
    PluginOptions(enableVerification = enableVerification, enableGhostElimination = enableGhostElimination)
  }

  private def parseBoolean(str: String): Option[Boolean] =
    str match {
      case "false" | "no" => Some(false)
      case "true" | "yes" => Some(true)
      case _ => None
    }

  private class ExtractionAndVerification extends PluginPhase {
    override val phaseName = "stainless"
    override val runsAfter = Set(Pickler.name)
    override val runsBefore = Set(FirstTransform.name)

    private var extraction: Option[StainlessExtraction] = None
    private var callback: Option[CallBack] = None
    private var exportedSymsMapping: ExportedSymbolsMapping = ExportedSymbolsMapping.empty

    // This method id called for every compilation unit, and in the same thread.
    // It is called within super.runOn.
    override def run(using DottyContext): Unit =
      extraction.get.extractUnit(exportedSymsMapping).foreach(extracted =>
        callback.get(extracted.file, extracted.unit, extracted.classes, extracted.functions, extracted.typeDefs))

    override def runOn(units: List[CompilationUnit])(using dottyCtx: DottyContext): List[CompilationUnit] = {
      val mainHelper = new stainless.MainHelpers {
        override val factory = new frontend.FrontendFactory{
          override def apply(ctx: Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
            sys.error("stainless.MainHelpers#factory should never be called from the dotty plugin")
          override protected val libraryPaths: Seq[String] = Seq.empty
        }
      }
      val inoxCtx = {
        val base = mainHelper.getConfigContext(inox.Options.empty)(using new stainless.PlainTextReporter(Set.empty))
        val adapter = new ReporterAdapter(base.reporter.debugSections)
        inox.Context(
          reporter         = adapter,
          interruptManager = new inox.utils.InterruptManager(adapter),
          options          = base.options,
          timers           = base.timers,
        )
      }
      val cb = stainless.frontend.getCallBack(using inoxCtx)
      // Not pretty at all... Oh well...
      callback = Some(cb)
      extraction = Some(new StainlessExtraction(inoxCtx))
      exportedSymsMapping = Utils.exportedSymbolsMapping(inoxCtx, this.start, units)

      cb.beginExtractions()
      val unitRes = super.runOn(units)
      cb.endExtractions()
      cb.join()

      val report = cb.getReport
      report foreach { report =>
        report.emit(inoxCtx)
      }

      unitRes
    }
  }

  class ReporterAdapter(debugSections: Set[DebugSection])(using dottyCtx: DottyContext) extends inox.PlainTextReporter(debugSections) {
    import dotty.tools.io._
    import Diagnostic._
    import Message._

    private def toSourceFile(file: java.io.File): SourceFile =
      SourceFile(AbstractFile.getFile(file.getPath), scala.io.Codec.UTF8)

    private def toDottyPos(pos: InoxPosition.Position): SourcePosition = pos match {
      case InoxPosition.NoPosition =>
        NoSourcePosition

      case InoxPosition.OffsetPosition(_, _, point, file) =>
        SourcePosition(toSourceFile(file), Spans.Span(point, point, point))

      case InoxPosition.RangePosition(_, _, pointFrom, _, _, pointTo, file) =>
        SourcePosition(toSourceFile(file), Spans.Span(pointFrom, pointFrom, pointTo))
    }

    override def clearProgress(): Unit = ()

    override def doEmit(message: Message): Unit = {
      val pos = toDottyPos(message.position)

      message.msg match {
        case msg: ReportMessage =>
          msg.emit(this)

        case msg: String =>
          message.severity match {
            case INFO                     => dottyCtx.reporter.report(Info(msg, pos))
            case WARNING                  => dottyCtx.reporter.report(Warning(msg.toMessage, pos))
            case ERROR | FATAL | INTERNAL => dottyCtx.reporter.report(Diagnostic.Error(msg, pos))
            case _                        => dottyCtx.reporter.report(Info(msg, pos)) // DEBUG messages are at reported at INFO level
          }

        case _ => ()
      }
    }
  }
}
