/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import io.circe._

import scala.concurrent.Future
import scala.util.{ Success, Failure }

object TerminationComponent extends Component {
  override val name = "termination"
  override val description = "Check program termination."

  override type Report = TerminationReport
  override type Analysis = TerminationAnalysis

  override val lowering = {
    class LoweringImpl(override val s: extraction.trees.type,
                       override val t: extraction.trees.type)
      extends inox.transformers.SymbolTransformer {
      override def transform(syms: s.Symbols): t.Symbols = syms
    }
    new LoweringImpl(extraction.trees, extraction.trees)
  }

  override def run(pipeline: extraction.StainlessPipeline)(using inox.Context) = {
    new TerminationRun(pipeline)
  }
}

class TerminationRun private(override val component: TerminationComponent.type,
                             override val trees: stainless.trees.type,
                             override val pipeline: extraction.StainlessPipeline)
                            (using override val context: inox.Context)
  extends ComponentRun {

  def this(pipeline: extraction.StainlessPipeline)(using inox.Context) =
    this(TerminationComponent, stainless.trees, pipeline)

  import component.{Report, Analysis}

  override def parse(json: Json): Report = TerminationReport.parse(json)

  private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis] = {
    import trees._
    import context.{given, _}

    val p = inox.Program(trees)(symbols)

    val res = functions map { id =>
      val fd = symbols.getFunction(id)
      fd -> fd.flags.collectFirst { case TerminationStatus(status) => status }.get
    }

    Future.successful(new TerminationAnalysis {
      override val program: p.type = p
      override val results: Map[p.trees.FunDef, TerminationReport.Status] = res.toMap
      override val sources = functions.toSet
    })
  }
}
