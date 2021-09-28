/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import io.circe._

import scala.concurrent.Future
import scala.language.existentials

import stainless.extraction._
import stainless.extraction.utils.DebugSymbols
import stainless.termination.MeasureInference

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strict-arithmetic", true)

/**
 * Generate VC via the System FR type-checker instead of the ad-hoc DefaultTactic.
 */
object optTypeChecker extends inox.FlagOptionDef("type-checker", true)

/**
 * Verify program using Coq
 */
object optCoq extends inox.FlagOptionDef("coq", false)

/** When enabled, do not verify verification conditions */
object optAdmitVCs extends inox.FlagOptionDef("admit-vcs", false)


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
} with ComponentRun { self =>

  import component.{Report, Analysis}

  override def parse(json: Json): Report = VerificationReport.parse(json)

  override protected def createPipeline = {
    pipeline andThen
    extraction.utils.DebugPipeline("MeasureInference", MeasureInference(extraction.trees)) andThen
    extraction.utils.DebugPipeline("PartialEvaluation", PartialEvaluation(extraction.trees))
  }

  implicit val debugSection = DebugSectionVerification

  private[this] val debugAssertions = new DebugSymbols {
    val name = "AssertionInjector"
    val context = self.context
    val s: self.trees.type = self.trees
    val t: self.trees.type = self.trees
  }

  private[stainless] def execute(functions0: Seq[Identifier], symbols: trees.Symbols): Future[VerificationAnalysis] = {
    import context._

    val functions = functions0.filterNot(fid => symbols.getFunction(fid).flags.contains(trees.DropVCs))
    val p = inox.Program(trees)(symbols)

    if (context.options.findOptionOrDefault(optCoq)) {
      CoqVerificationChecker.verify(functions, p, context)
    } else {

      val assertions = AssertionInjector(p, context)
      val assertionEncoder = inox.transformers.ProgramEncoder(p)(assertions)

      if (debugAssertions.isEnabled) {
        debugAssertions.debugEncoder(assertionEncoder)
      }

      if (!functions.isEmpty) {
        reporter.debug(s"Generating VCs for functions: ${functions map { _.uniqueName } mkString ", "}")
      }

      val vcGenEncoder = assertionEncoder

      val vcs = if (context.options.findOptionOrDefault(optTypeChecker))
        context.timers.verification.get("type-checker").run {
          TypeChecker(vcGenEncoder.targetProgram, context).checkFunctionsAndADTs(functions)
        }
      else
        VerificationGenerator.gen(vcGenEncoder.targetProgram, context)(functions)

      if (!functions.isEmpty) {
        reporter.debug(s"Finished generating VCs")
      }

      val res =
        if (context.options.findOptionOrDefault(optAdmitVCs)) {
          Future(vcs.map(vc => vc -> VCResult(VCStatus.Admitted, None, None)).toMap)
        } else {
          VerificationChecker.verify(assertionEncoder.targetProgram, context)(vcs).map(_.view.mapValues {
            case VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s, t) =>
              VCResult(VCStatus.Invalid(VCStatus.CounterExample(model.encode(assertionEncoder.reverse))), s, t)
            case res => res.asInstanceOf[VCResult[p.Model]]
          }.toMap)
        }

      res.map(r => new VerificationAnalysis {
        override val program: p.type = p
        override val context = VerificationRun.this.context
        override val sources = functions.toSet
        override val results = r
      })

    }
  }
}

