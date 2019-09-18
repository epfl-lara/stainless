/* Copyright 2009-2019 EPFL, Lausanne */

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

    override def transform(syms: s.Symbols): t.Symbols = {
      syms.transform(DecreasesTransformer(s)(syms))
    }
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
    val c = TerminationChecker(p, context)

    val res = functions map { id =>
      val fd = symbols.getFunction(id)
      val (time, tryStatus) = timers.termination.runAndGetTime { c.terminates(fd) }
      tryStatus match {
        case Success(status) => fd -> (status, time)
        case Failure(e) => reporter.internalError(e)
      }
    }

    Future.successful(new TerminationAnalysis {
      override val checker: c.type = c
      override val results: Map[p.trees.FunDef, (c.TerminationGuarantee, Long)] = res.toMap
      override val sources = functions.toSet
    })
  }
}

