/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funsuite.AnyFunSuite

/** Checks that the test suites, which load their benchmarks with
 *  [[InputUtils.loadFiles]], fail and show the error of the compiler when a
 *  benchmark does not compile.
 */
class CompilationErrorsSuite extends AnyFunSuite with InputUtils:

  test("loading a file that does not compile fails with the compiler's error") {
    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.given

    val error = intercept[ExtractionError](load(Seq("!")))

    assert(error.errs.exists(_.contains("Illegal start of toplevel definition")))
  }
