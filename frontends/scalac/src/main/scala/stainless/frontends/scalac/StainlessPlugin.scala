package stainless
package frontends
package scalac

import scala.reflect.io.AbstractFile
import scala.reflect.internal.util.{NoPosition, Position, BatchSourceFile}
import scala.tools.nsc.Global
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.reporters.{Reporter => ScalacReporter}
import inox.DebugSection
import inox.{utils => InoxPosition}
import stainless.frontend.CallBack

object StainlessPlugin {
  val PluginName = "stainless"
  val PluginDescription = "Inject Stainless verification pipeline"
  val EnableVerificationOptionName = "verify:"
  val EnableGhostEliminationOptionName = "ghost-elim:"
}

case class PluginOptions(
  var enableVerification: Boolean,
  var enableGhostElimination: Boolean,
) {
  def enabled: Boolean = enableVerification || enableGhostElimination
}

class StainlessPlugin(val global: Global) extends Plugin {
  import StainlessPlugin._

  val mainHelper = new stainless.MainHelpers {
    override lazy val factory = {
      sys.error("stainless.MainHelpers#factory should never be called from the scalac plugin")
    }
  }

  val stainlessContext: inox.Context = {
    implicit val reporter = new stainless.PlainTextReporter(Set.empty)
    mainHelper.getConfigContext(OptionOrDefault.Default)
  }

  override val name: String = PluginName
  override val description: String = PluginDescription
  val pluginOptions: PluginOptions = PluginOptions(true, true)

  override val components: List[PluginComponent] = List(
    new StainlessPluginComponent(pluginOptions, global, stainlessContext),
    new GhostPluginComponent(pluginOptions, global),
  )

  override def init(options: List[String], error: String => Unit): Boolean = {
    for (option <- options) {
      if (option.startsWith(EnableVerificationOptionName)) {
        val value = option.substring(EnableVerificationOptionName.length)
        parseBoolean(value, error) foreach { value =>
          pluginOptions.enableVerification = value
        }
      } else if (option.startsWith(EnableGhostEliminationOptionName)) {
        val value = option.substring(EnableGhostEliminationOptionName.length)
        parseBoolean(value, error).foreach { value =>
          pluginOptions.enableGhostElimination = value
        }
      } else {
        error("Unknown option for Stainless plugin: " + option)
      }
    }

    pluginOptions.enabled
  }

  private def parseBoolean(str: String, error: String => Unit): Option[Boolean] = {
    str match {
      case "false" => Some(false)
      case "true" => Some(true)
      case other =>
        error(s"Invalid boolean value: $other")
        None
    }
  }
}

class StainlessPluginComponent(
  val pluginOptions: PluginOptions,
  val global: Global,
  val stainlessContext: inox.Context
) extends PluginComponent with StainlessExtraction {

  override def enabled: Boolean = pluginOptions.enableVerification

  override implicit val ctx: inox.Context = {
    val adapter = new ReporterAdapter(global.reporter, stainlessContext.reporter.debugSections)

    inox.Context(
      reporter         = adapter,
      interruptManager = new inox.utils.InterruptManager(adapter),
      options          = stainlessContext.options,
      timers           = stainlessContext.timers,
    )
  }

  override protected val callback: CallBack = stainless.frontend.getCallBack(ctx)

  override protected val cache: SymbolMapping = new SymbolMapping

  override val phaseName      = "stainless"
  override val runsAfter      = List("typer")
  override val runsRightAfter = None
  override val runsBefore     = List("patmat")

  override def onRun(run: () => Unit): Unit = {
    callback.beginExtractions()
    run()
    callback.endExtractions()
    callback.join()

    val report = callback.getReport
    report foreach { report =>
      report.emit(ctx)
    }
  }
}

class GhostPluginComponent(
  val pluginOptions: PluginOptions,
  val global: Global,
) extends PluginComponent with GhostAccessRewriter {
  override val runsAfter = List[String]("pickler")
}

class ReporterAdapter(underlying: ScalacReporter, debugSections: Set[DebugSection]) extends inox.PlainTextReporter(debugSections) {
  private def toSourceFile(file: java.io.File): BatchSourceFile = {
    new BatchSourceFile(AbstractFile.getFile(file))
  }

  private def toScalaPos(pos: InoxPosition.Position): Position = pos match {
    case InoxPosition.NoPosition =>
      NoPosition

    case InoxPosition.OffsetPosition(_, _, point, file) =>
      Position.offset(toSourceFile(file), point)

    case InoxPosition.RangePosition(_, _, pointFrom, _, _, pointTo, file) =>
      Position.range(toSourceFile(file), pointFrom, pointFrom, pointTo)
  }

  override def emit(message: Message): Unit = {
    val pos = toScalaPos(message.position)

    message.msg match {
      case msg: ReportMessage =>
        msg.emit(this)

      case msg: String =>
        message.severity match {
          case INFO                     => underlying.echo(pos, msg)
          case WARNING                  => underlying.warning(pos, msg)
          case ERROR | FATAL | INTERNAL => underlying.error(pos, msg)
          case _                        => underlying.echo(pos, msg) // DEBUG messages are at reported at INFO level
        }

      case _ => ()
    }
  }
}
