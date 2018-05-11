/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.Future
import scala.language.existentials

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strict-arithmetic", false)
object optCoq extends inox.FlagOptionDef("coq", false)

object VerificationComponent extends SimpleComponent {
  override val name = "verification"
  override val description = "Verification of function contracts"

  override val trees: stainless.trees.type = stainless.trees

  override type Analysis = VerificationAnalysis

  override val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  override def apply(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Future[VerificationAnalysis] = {
    if (ctx.options.findOptionOrDefault(optCoq)) {
      CoqVerificationChecker.verify(funs, p, ctx)
    } else {
    import ctx._

    val assertions = AssertionInjector(p, ctx)
    val chooses = ChooseInjector(p)

    reporter.debug(s"Generating VCs for those functions: ${funs map { _.uniqueName } mkString ", "}")

    // We do not need to encode empty trees as chooses when generating the VCs,
    // as we rely on having empty trees to filter out some VCs.
    val assertionEncoder = inox.ast.ProgramEncoder(p)(assertions)
    val vcs = VerificationGenerator.gen(assertionEncoder.targetProgram, ctx)(funs)

    // We need the full encoder when verifying VCs otherwise we might end up evaluating empty trees.
    val encoder = inox.ast.ProgramEncoder(p)(assertions andThen chooses)

    val res = VerificationChecker.verify(encoder.targetProgram, ctx)(vcs).map(_.mapValues {
      case VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s, t) =>
        VCResult(VCStatus.Invalid(VCStatus.CounterExample(model.encode(encoder.reverse))), s, t)
      case res => res.asInstanceOf[VCResult[p.Model]]
    })

    res.map(r => new VerificationAnalysis {
      override val program: p.type = p
      override val sources = funs.toSet
      override val results = r
    })
    }
  }
}

