package stainless
package testgen

import io.circe.Json
import stainless.extraction._
import stainless.extraction.xlang.{trees => xt}
import stainless.verification._
import stainless.verification.VerificationComponent.{Analysis, Report}

import scala.concurrent.Future

object ScalaTestGenComponent extends Component {
  override val name = "testgen"
  override val description = "(Experimental) Attempt to create Scala test cases from reported counter-examples (implies --batched)"

  override type Report = VerificationComponent.Report
  override type Analysis = VerificationComponent.Analysis

  override val lowering = VerificationComponent.lowering

  override def run(pipeline: StainlessPipeline)(using inox.Context): ScalaTestGenRun = {
    new ScalaTestGenRun(pipeline)
  }
}

class ScalaTestGenRun private(override val component: ScalaTestGenComponent.type,
                              override val trees: stainless.trees.type,
                              override val pipeline: StainlessPipeline,
                              val underlyingRun: VerificationRun)
                             (using override val context: inox.Context) extends ComponentRun {

  import component.{Analysis, Report}

  def this(pipeline: StainlessPipeline)(using inox.Context) =
    this(ScalaTestGenComponent, stainless.trees, pipeline, new VerificationRun(pipeline))

  override def createPipeline = underlyingRun.createPipeline

  override def parse(json: Json): VerificationReport = underlyingRun.parse(json)

  override def apply(ids: Seq[Identifier], symbols: xt.Symbols): Future[Analysis] = {
    underlyingRun(ids, symbols).map { res =>
      ScalaTestGen.generateTestCases(symbols)(res.program)(res.results)
      res
    }
  }

  override private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis] =
    sys.error("Unreachable because def apply was overridden")
}