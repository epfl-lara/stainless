/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import extraction.utils.optDebugPhases
import org.scalatest.funsuite.AnyFunSuite

/** Checks that `--debug-phases` accepts the names of the phases of the
 *  pipelines, which it validates against [[extraction.phases]].
 */
class DebugPhasesSuite extends AnyFunSuite:

  given inox.Context = TestContext.empty

  test("--debug-phases accepts the phases that extraction.phases missed (#1846)"):
    for name <- Seq("ConstructsUsage", "MethodsLowering", "TrimSymbols", "TailRecElim") do
      assert(optDebugPhases.parser(name) == Some(Seq(name)), name)

  test("--debug-phases rejects ComputeDependencies, which no longer exists (#1846)"):
    assert(optDebugPhases.parser("ComputeDependencies") == None)

  test("the pipelines only name phases listed in extraction.phases"):
    // `NamedPipeline` and `NamedLeonPhase` require their name to be listed: building the pipelines checks them
    verification.VerificationComponent.run(extraction.pipeline)
    genc.GenCRun.pipelineBegin
    genc.GenerateC.pipeline(extraction.throwing.trees.NoSymbols)
