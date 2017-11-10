/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{trees => xt}

import scala.language.existentials

/**
 * Strict Arithmetic Mode:
 *
 * Add assertions for integer overflow checking and other unexpected behaviour (e.g. x << 65).
 */
object optStrictArithmetic extends inox.FlagOptionDef("strict-arithmetic", false)

object VerificationComponent extends SimpleComponent { self =>
  override val name = "verification"
  override val description = "Verification of function contracts"

  override val trees: stainless.trees.type = stainless.trees

  override type Analysis = VerificationAnalysis

  override val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = DebugSectionVerification

  override def extract(program: Program { val trees: xt.type }, ctx: inox.Context): Program { val trees: self.trees.type } = {
    val extractedProgram = super.extract(program, ctx)
    forceEval.ForceEvaluation(extractedProgram, ctx).targetProgram
  }

  private def check(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Map[VC[p.trees.type], VCResult[p.Model]] = {
    val injector = AssertionInjector(p, ctx)
    val encoder = inox.ast.ProgramEncoder(p)(injector)

    import ctx._
    import encoder.targetProgram._
    import encoder.targetProgram.trees._
    import encoder.targetProgram.symbols._

    val toVerify = funs.sortBy(getFunction(_).getPos)
    ctx.reporter.debug(s"Generating VCs for those functions: ${toVerify map { _.uniqueName } mkString ", "}")

    for (id <- toVerify) {
      if (getFunction(id).flags contains "library") {
        val fullName = id.fullName
        reporter.warning(s"Forcing verification of $fullName which was assumed verified")
      }
    }

    val vcs = VerificationGenerator.gen(encoder.targetProgram, ctx)(toVerify)

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
      override val results = res
    }
  }
}

