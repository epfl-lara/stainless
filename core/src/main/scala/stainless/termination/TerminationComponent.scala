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

  override object lowering extends inox.transformers.SymbolTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees

    override def transform(syms: s.Symbols): t.Symbols = syms
  }

  override def run(pipeline: extraction.StainlessPipeline)(implicit ctx: inox.Context) = {
    new TerminationRun(pipeline)
  }
}

class TerminationRun(override val pipeline: extraction.StainlessPipeline)
                    (override implicit val context: inox.Context) extends {
  override val component = TerminationComponent
  override val trees: stainless.trees.type = stainless.trees
} with ComponentRun {

  import component.{Report, Analysis}

  override def parse(json: Json): Report = TerminationReport.parse(json)

  private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis] = {
    import trees._
    import context._

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
