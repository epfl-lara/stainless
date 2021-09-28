/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.throwing.trees._

import phases._

object GenerateC {

  def pipeline(arrayLengthsMap: Map[Identifier, Int])(implicit ctx: inox.Context) =
    NamedLeonPhase("GhostElimination", GhostEliminationPhase(ctx)) andThen
    NamedLeonPhase("TrimSymbols", TrimSymbols(ctx)) andThen
    NamedLeonPhase("ComputeFunCtx", LeonPipeline.both(NoopPhase[Symbols], ComputeFunCtxPhase(ctx))) andThen
    NamedLeonPhase("Scala2IR", Scala2IRPhase(arrayLengthsMap)) andThen
    NamedLeonPhase("Normalisation", NormalisationPhase(ctx)) andThen
    NamedLeonPhase("Lifting", LiftingPhase(ctx)) andThen
    NamedLeonPhase("Referencing", ReferencingPhase(ctx)) andThen
    NamedLeonPhase("StructInlining", StructInliningPhase(ctx)) andThen
    NamedLeonPhase("IR2C", IR2CPhase(ctx)) andThen
    CFileOutputPhase(ctx)

  def run(symbols: Symbols)(implicit ctx: inox.Context) = {
    // extract lengths before `GhostElimination` erases them
    val arrayLengthsMap = ArraysLengthsExtraction.get(symbols)
    pipeline(arrayLengthsMap).run(symbols)
  }

}
