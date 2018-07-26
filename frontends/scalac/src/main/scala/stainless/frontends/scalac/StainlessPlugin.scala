package stainless.frontends.scalac

import scala.reflect.internal.util.NoPosition
import scala.tools.nsc.Global
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.reporters.{Reporter => ScalacReporter}
import inox.{Context => InoxContext, DefaultReporter => InoxDefaultReporter}
import inox.DebugSection
import stainless.frontend.CallBack

class StainlessPlugin(override val global: Global) extends Plugin {
  override val name: String = "stainless-plugin"
  override val description: String = "stainless scala compiler plugin"
  override val components: List[PluginComponent] = {
    List(new StainlessPluginComponent(global), new GhostPluginComponent(global))
  }
}

class StainlessPluginComponent(val global: Global) extends PluginComponent with StainlessExtraction {
  override implicit val ctx: inox.Context = {
    val adapter = new ReporterAdapter(global.reporter, Set())
    InoxContext.empty.copy(reporter = adapter)
  }
  override protected val callback: CallBack = stainless.frontend.getStainlessCallBack(ctx)
  override protected val cache: SymbolMapping = new SymbolMapping

  // FIXME: Mind the duplication with ScalaCompiler#stainlessExtraction. Should we extract the common bits?
  override val phaseName: String = "stainless"
  override val runsAfter = List[String]()
  override val runsRightAfter = Some("typer")
}

class GhostPluginComponent(val global: Global) extends PluginComponent with GhostAccessRewriter {
  override val runsAfter = List[String]("pickler")
}


class ReporterAdapter(underlying: ScalacReporter, debugSections: Set[DebugSection]) extends InoxDefaultReporter(debugSections) {
  // FIXME: Mapping of stainless -> scalac positions
  override def emit(msg: Message): Unit = {
    // FIXME: Reporting the message through the inox reporter shouldn't be needed. But without it the compilation error is
    //        not reported. Maybe this is because stainless stops after the first error?
    super.emit(msg)
    msg.severity match {
      case INFO => underlying.echo(NoPosition, msg.msg.toString)
      case WARNING => underlying.warning(NoPosition, msg.msg.toString)
      case ERROR | FATAL | INTERNAL => underlying.error(NoPosition, msg.msg.toString)
      case _ => underlying.echo(NoPosition, msg.msg.toString) // DEBUG messages are at reported at INFO level
    }
  }
}
