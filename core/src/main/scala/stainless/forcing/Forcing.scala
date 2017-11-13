/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package forcing

import inox.evaluators.EvaluationResults._

object DebugSectionForcing extends inox.DebugSection("forcing")

class Forcing(
  override val sourceProgram: StainlessProgram,
  val context: inox.Context
) extends inox.ast.ProgramTransformer { self =>

  import context._
  import sourceProgram._
  import sourceProgram.trees._
  import sourceProgram.symbols._
  import sourceProgram.trees.exprOps._

  override final object encoder extends IdentityTreeTransformer
  override final object decoder extends IdentityTreeTransformer

  implicit val debugSection = DebugSectionForcing

  implicit private val semantics = sourceProgram.getSemantics

  override final lazy val targetProgram: Program { val trees: sourceProgram.trees.type } = {
    inox.Program(sourceProgram.trees)(transform(sourceProgram.symbols))
  }

  object transformer extends IdentityTreeTransformer

  private def transform(syms: Symbols): Symbols = {
    NoSymbols
      .withADTs(symbols.adts.values.map(transformer.transform).toSeq)
      .withFunctions(symbols.functions.values.toSeq.map { fd =>
        transformer.transform(force(fd))
      })
  }

  private def force(fd: FunDef): FunDef = {
    if (!fd.flags.contains(Force))
      return fd

    val empty = NoTree(fd.returnType)

    reporter.debug(s"Forcing function ${fd.id}@${fd.getPos}...")

    val (pre, body, post) = breakDownSpecs(fd.fullBody)

    reporter.debug(s" - Before: ${body getOrElse empty}...")

    val forced = body match {
      case Some(b) =>
        Some(simplifyGround(b)(semantics, context))
      case None =>
        reporter.error("Cannot force an empty tree")
        None
    }

    reporter.debug(s" - After: ${forced getOrElse empty}")

    val forcedBody = reconstructSpecs(pre, forced, post, fd.returnType)

    fd.copy(
      fullBody = forcedBody,
      flags = fd.flags - Force
    )
  }
}

