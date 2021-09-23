/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.throwing.trees._

import phases._

object GenerateC {

  def pipeline(implicit ctx: inox.Context) =
    NamedLeonPhase("GhostEliminationPhase", GhostEliminationPhase(ctx)) andThen
    NamedLeonPhase("ComputeDependencies", ComputeDependenciesPhase(ctx)) andThen
    NamedLeonPhase("ComputeFunCtxPhase", LeonPipeline.both(NoopPhase[Symbols], ComputeFunCtxPhase(ctx))) andThen
    NamedLeonPhase("Scala2IRPhase", Scala2IRPhase(ctx)) andThen
    NamedLeonPhase("NormalisationPhase", NormalisationPhase(ctx)) andThen
    NamedLeonPhase("LiftingPhase", LiftingPhase(ctx)) andThen
    NamedLeonPhase("ReferencingPhase", ReferencingPhase(ctx)) andThen
    NamedLeonPhase("StructInliningPhase", StructInliningPhase(ctx)) andThen
    NamedLeonPhase("IR2CPhase", IR2CPhase(ctx)) andThen
    CFileOutputPhase(ctx)

  def run(symbols: Symbols)(implicit ctx: inox.Context) = pipeline.run(symbols)

}
