/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.language.existentials

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strict-arithmetic", false)

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

  private def check(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Map[VC[p.trees.type], VCResult[p.Model]] = {
    val assertions = AssertionInjector(p, ctx)
    val chooses = ChooseInjector(p)
    val encoder = inox.ast.ProgramEncoder(p)(assertions andThen chooses)

    import ctx._
    import encoder.targetProgram._
    import encoder.targetProgram.trees._
    import encoder.targetProgram.symbols._

    reporter.debug(s"Generating VCs for those functions: ${funs map { _.uniqueName } mkString ", "}")

    val vcs = VerificationGenerator.gen(encoder.targetProgram, ctx)(funs)

    VerificationChecker.verify(encoder.targetProgram, ctx)(vcs).mapValues {
      case VCResult(VCStatus.Invalid(model), s, t) =>
        VCResult(VCStatus.Invalid(model.encode(encoder.reverse)), s, t)
      case res => res.asInstanceOf[VCResult[p.Model]]
    }
  }

  override def apply(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): VerificationAnalysis = {
    val res = check(funs, p, ctx)

    new VerificationAnalysis {
      override val program: p.type = p
      override val sources = funs.toSet
      override val results = res
    }
  }
}

