package stainless.frontends.scalac

import scala.reflect.internal.util.NoPosition
import scala.tools.nsc.Global
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.reporters.{Reporter => ScalacReporter}
import inox.{Context => InoxContext, Reporter => InoxReporter}
import inox.DebugSection
import stainless.frontend.MasterCallBack

class StainlessPlugin(override val global: Global) extends Plugin {
  override val name: String = "stainless-plugin"
  override val description: String = "stainless scala compiler plugin"
  override val components: List[PluginComponent] = {
    List(new StainlessPluginComponent(global))
  }
}

class StainlessPluginComponent(val global: Global) extends PluginComponent with StainlessExtraction {
  override implicit val ctx: inox.Context = {
    val adapter = new ReporterAdapter(global.reporter, Set())
    InoxContext.empty.copy(reporter = adapter)
  }
  override protected val callback: MasterCallBack = stainless.frontend.getMasterCallBack(ctx)
  override protected val cache: SymbolMapping = new SymbolMapping

  // FIXME: Mind the duplication with ScalaCompiler#stainlessExtraction. Should we extract the common bits?
  override val phaseName: String = "stainless"
  override val runsAfter = List[String]("refchecks")
}

class ReporterAdapter(underlying: ScalacReporter, debugSections: Set[DebugSection]) extends InoxReporter(debugSections) {
  // FIXME: Mapping of stainless -> scalac positions
  override def emit(msg: Message): Unit = msg.severity match {
    case INFO => underlying.echo(NoPosition, msg.msg.toString)
    case WARNING => underlying.warning(NoPosition, msg.msg.toString)
    case ERROR  | FATAL | INTERNAL => underlying.error(NoPosition, msg.msg.toString)
    case _ => underlying.echo(NoPosition, msg.msg.toString) // DEBUG messages are at reported at INFO level
  }
}
