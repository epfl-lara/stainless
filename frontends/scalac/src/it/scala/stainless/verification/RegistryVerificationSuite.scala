/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

/*
 * A special test for --functions=therorem --check-models.
 *
 * The goal is to tests the combination of the Registry
 * and the VerificationComponent under these options.
 */
class RegistryVerificationSuite extends ComponentTestSuite {

  val component = VerificationComponent

  override def configurations = super.configurations.map {
    seq => inox.solvers.optCheckModels(true) +: optFunctions("theorem" :: Nil) +: seq
  }

  test(s"special --functions=theorem --check-models test", ctx => filter(ctx, "")) { ctx =>
    val fs = resourceFiles("extraction/registry", _.endsWith(".scala"))
    assert(fs.size == 1 && fs.head.getName == "TestFunctionsOption.scala", "Test files were changed!")
    val Seq(file) = fs

    val (uName, funs, program) = extractOne(file.getPath, ctx, useFilter = true)
    assert(uName == "TestFunctionsOption")
    val analysis = component.apply(funs, program, ctx)
    val stats = analysis.toReport.stats

    // analysis.vrs foreach { r => info(r.toString) }

    assert(stats.valid   == 0, "No VC is expected to be valid for this test.")
    assert(stats.unknown == 0, "No VC is expected to be unknown for this test.")
    assert(stats.invalid == 1, "Exactly one VC is expected to be invalid for this test.")
  }
}

