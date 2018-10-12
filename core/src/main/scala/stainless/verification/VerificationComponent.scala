/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import io.circe._

import scala.concurrent.Future
import scala.language.existentials

import extraction._

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strict-arithmetic", false)

object VerificationComponent extends Component {
  override val name = "verification"
  override val description = "Verification of function contracts"

  override type Report = VerificationReport
  override type Analysis = VerificationAnalysis

  override val lowering = inox.transformers.SymbolTransformer(new transformers.TreeTransformer {
    val s: trees.type = trees
    val t: trees.type = trees
  })

  override def run(pipeline: StainlessPipeline)(implicit ctx: inox.Context) = {
    new VerificationRun(pipeline)
  }
}

class VerificationRun(override val pipeline: StainlessPipeline)
                     (override implicit val context: inox.Context) extends {
  override val component = VerificationComponent
  override val trees: stainless.trees.type = stainless.trees
} with ComponentRun {

  import component.{Report, Analysis}

  override def parse(json: Json): Report = VerificationReport.parse(json)

  override protected def createPipeline = pipeline andThen lowering andThen
    extraction.utils.DebugPipeline("PartialEvaluation", PartialEvaluation(extraction.trees))

  implicit val debugSection = DebugSectionVerification

  override def apply(functions: Seq[Identifier], symbols: trees.Symbols): Future[VerificationAnalysis] = {
    import context._

    val p = inox.Program(trees)(symbols)

    val assertions = AssertionInjector(p, context)
    val chooses = ChooseInjector(p)

    reporter.debug(s"Generating VCs for those functions: ${functions map { _.uniqueName } mkString ", "}")

    // We do not need to encode empty trees as chooses when generating the VCs,
    // as we rely on having empty trees to filter out some VCs.
    val assertionEncoder = inox.transformers.ProgramEncoder(p)(assertions)
    val vcs = VerificationGenerator.gen(assertionEncoder.targetProgram, context)(functions)

    // We need the full encoder when verifying VCs otherwise we might end up evaluating empty trees.
    val encoder = inox.transformers.ProgramEncoder(p)(assertions andThen chooses)

    val res = VerificationChecker.verify(encoder.targetProgram, context)(vcs).map(_.mapValues {
      case VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s, t) =>
        VCResult(VCStatus.Invalid(VCStatus.CounterExample(model.encode(encoder.reverse))), s, t)
      case res => res.asInstanceOf[VCResult[p.Model]]
    })

    res.map(r => new VerificationAnalysis {
      override val program: p.type = p
      override val context = VerificationRun.this.context
      override val sources = functions.toSet
      override val results = r
    })
  }
}

