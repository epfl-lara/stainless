/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import io.circe._

import scala.concurrent.Future

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

  override val lowering = {
    class LoweringImpl(override val s: trees.type, override val t: trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    inox.transformers.SymbolTransformer(new LoweringImpl(trees, trees))
  }

  override def run(pipeline: StainlessPipeline)(using inox.Context): VerificationRun = {
    new VerificationRun(pipeline)
  }
}

class VerificationRun private(override val component: VerificationComponent.type,
                              override val trees: stainless.trees.type,
                              override val pipeline: StainlessPipeline)
                             (using override val context: inox.Context) extends ComponentRun { self =>
  def this(pipeline: StainlessPipeline)(using inox.Context) =
    this(VerificationComponent, stainless.trees, pipeline)

  import component.{Report, Analysis}
  import extraction.given

  override def parse(json: Json): Report = VerificationReport.parse(json)

  override def createPipeline = {
    pipeline `andThen`
    extraction.utils.NamedPipeline("MeasureInference", MeasureInference(extraction.trees)) `andThen`
    extraction.utils.NamedPipeline("PartialEvaluation", PartialEvaluation(extraction.trees))
  }

  given givenDebugSection: DebugSectionVerification.type = DebugSectionVerification

  private val debugAssertions = new DebugSymbols {
    val name = "AssertionInjector"
    val context = self.context
    val s: self.trees.type = self.trees
    val t: self.trees.type = self.trees
  }

  override private[stainless] def execute(functions0: Seq[Identifier], symbols: trees.Symbols, exSummary: ExtractionSummary): Future[VerificationAnalysis] = {
    import context._

    val functions = functions0.filterNot(fid => symbols.getFunction(fid).flags.contains(trees.DropVCs))
    val p = inox.Program(trees)(symbols)

    if (context.options.findOptionOrDefault(optCoq)) {
      val vcResult = CoqVerificationChecker.verify(functions, p, context)
      Future.successful(new VerificationAnalysis {
        override val program: p.type = p
        override val context = VerificationRun.this.context
        override val sources = functions.toSet
        override val results = vcResult
        override val extractionSummary = exSummary
      })
    } else {
      val assertions = AssertionInjector(p, context)
      val assertionEncoder = inox.transformers.ProgramEncoder(p)(assertions)

      if (debugAssertions.isEnabled) {
        debugAssertions.debugEncoder(assertionEncoder)
      }

      if (!functions.isEmpty) {
        val plural = if (functions.size == 1) "" else "s"
        val msg = {
          if (reporter.isDebugEnabled) s"Generating VCs for function$plural: ${functions map { _.uniqueName } mkString ", "}..."
          else s"Generating VCs for ${functions.size} function$plural..."
        }
        reportVCProgress(msg)
      }

      val vcGenEncoder = assertionEncoder

      val vcs = context.timers.verification.get("type-checker").run {
        TypeChecker(vcGenEncoder.targetProgram, context).checkFunctionsAndADTs(functions)
      }

      if (!functions.isEmpty) {
        reportVCProgress(s"Finished generating VCs")
      }
      val opaqueEncoder = inox.transformers.ProgramEncoder(vcGenEncoder.targetProgram)(OpaqueChooseInjector(vcGenEncoder.targetProgram))
      val res: Future[Map[VC[p.trees.type], VCResult[p.Model]]] =
        if (context.options.findOptionOrDefault(optAdmitVCs)) {
          Future(vcs.map(vc => vc -> VCResult(VCStatus.Admitted, None, None, None)).toMap)
        } else {
          VerificationChecker.verify(opaqueEncoder.targetProgram, context)(vcs).map(_.view.mapValues {
            case VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s, t, smtid) =>
              VCResult(VCStatus.Invalid(VCStatus.CounterExample(model.encode(opaqueEncoder.reverse.andThen(vcGenEncoder.reverse)))), s, t, smtid)
            case res => res.asInstanceOf[VCResult[p.Model]]
          }.toMap)
        }

      res.map(r => new VerificationAnalysis {
        override val program: p.type = p
        override val context = VerificationRun.this.context
        override val sources = functions.toSet
        override val results = r
        override val extractionSummary = exSummary
      })
    }
  }

  private case object VCProgressTag
  private def reportVCProgress(msg: String): Unit = {
    import context._
    import context.reporter._
    emit(ProgressMessage(INFO, VCProgressTag, msg))
  }
}

