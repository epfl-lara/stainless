/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

// import purescala.Definitions.{ Program }
// import utils.{ DebugSectionTrees }

import extraction.throwing.trees._

import phases._

object GenerateCPhase extends LeonPipeline[Symbols, CAST.Prog] {

  val name = "Generate C"
  val description = "Preprocess and convert Stainless's AST to C"

  val pipeline =
    NamedLeonPhase("ComputeDependencies", ComputeDependenciesPhase) andThen
    NamedLeonPhase("ComputeFunCtxPhase", LeonPipeline.both(NoopPhase[Dependencies], ComputeFunCtxPhase)) andThen
    NamedLeonPhase("Scala2IRPhase", Scala2IRPhase) andThen
    NamedLeonPhase("NormalisationPhase", NormalisationPhase) andThen
    NamedLeonPhase("LiftingPhase", LiftingPhase) andThen
    NamedLeonPhase("ReferencingPhase", ReferencingPhase) andThen
    NamedLeonPhase("IR2CPhase", IR2CPhase) andThen
    CFileOutputPhase

  def run(ctx: inox.Context, symbols: Symbols) = pipeline.run(ctx, symbols)

}
