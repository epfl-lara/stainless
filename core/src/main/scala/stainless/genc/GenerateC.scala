/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.throwing.trees._

import phases._

object GenerateC {

  def pipeline(arrayLengthsMap: Map[Identifier, Int])(using inox.Context) =
    NamedLeonPhase("GhostElimination", new GhostEliminationPhase) andThen
    NamedLeonPhase("TrimSymbols", new TrimSymbols) andThen
    NamedLeonPhase("ComputeFunCtx", LeonPipeline.both(NoopPhase[Symbols], new ComputeFunCtxPhase)) andThen
    NamedLeonPhase("Scala2IR", Scala2IRPhase(arrayLengthsMap)) andThen
    NamedLeonPhase("Normalisation", new NormalisationPhase) andThen
    NamedLeonPhase("Lifting", new LiftingPhase) andThen
    NamedLeonPhase("Referencing", new ReferencingPhase) andThen
    NamedLeonPhase("StructInlining", new StructInliningPhase) andThen
    NamedLeonPhase("IR2C", new IR2CPhase) andThen
    new CFileOutputPhase

  def run(symbols: Symbols)(using ctx: inox.Context) = {
    // extract lengths before `GhostElimination` erases them
    val arrayLengthsMap = ArraysLengthsExtraction.get(symbols)
    pipeline(arrayLengthsMap).run(symbols)
  }

}
