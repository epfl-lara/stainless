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

class StainlessPlugin(override val global: Global) extends Plugin {
  val stainlessContext: inox.Context = stainless.Context.empty

  override val name: String = "stainless-plugin"
  override val description: String = "stainless scala compiler plugin"
  override val components: List[PluginComponent] = List(
    new StainlessPluginComponent(global, stainlessContext),
    new GhostPluginComponent(global)
  )
}

class StainlessPluginComponent(
  val global: Global,
  val stainlessContext: inox.Context = stainless.Context.empty
) extends PluginComponent with StainlessExtraction {
  override implicit val ctx: inox.Context = {
    val adapter = new ReporterAdapter(global.reporter, Set())
    stainlessContext.copy(reporter = adapter)
  }

  override protected val callback: CallBack = stainless.frontend.getCallBack(ctx)

  override protected val cache: SymbolMapping = new SymbolMapping

  // FIXME: Mind the duplication with ScalaCompiler#stainlessExtraction. Should we extract the common bits?
  override val phaseName: String = "stainless"
  override val runsAfter = List[String]()
  override val runsRightAfter = Some("typer")
}

class GhostPluginComponent(val global: Global) extends PluginComponent with GhostAccessRewriter {
  override val runsAfter = List[String]("pickler")
}

class ReporterAdapter(underlying: ScalacReporter, debugSections: Set[DebugSection]) extends inox.DefaultReporter(debugSections) {
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
