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

  implicit val debugSection = DebugSectionCoq

  private def check(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Map[VC[p.trees.type], VCResult[p.Model]] = {
    if (ctx.options.findOptionOrDefault(optCoq)) {
      CoqVerificationChecker.verify(funs, p, ctx)
    } else {
      val injector = AssertionInjector(p, ctx)
      val encoder = inox.ast.ProgramEncoder(p)(injector)

      import ctx._
      import encoder.targetProgram._
      import encoder.targetProgram.trees._
      import encoder.targetProgram.symbols._

      val toVerify = filter(p, ctx)(funs) map { _.id }

      reporter.debug(s"Generating VCs for those functions: ${toVerify map { _.uniqueName } mkString ", "}")

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
      override val sources = funs.toSet
      override val results = res
    }
  }
}

