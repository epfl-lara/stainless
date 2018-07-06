/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }

import org.scalatest._

import scala.concurrent.Await
import scala.concurrent.duration._

/*
 * A special test for --functions=therorem --check-models.
 *
 * The goal is to tests the combination of the Registry
 * and the VerificationComponent under these options.
 */
class RegistryVerificationSuite extends FunSuite with InputUtils {

  test(s"special --functions=theorem --check-models test") {
    val options = Seq(inox.solvers.optCheckModels(true), optFunctions("theorem" :: Nil))
    implicit val ctx = stainless.TestContext(inox.Options(options))
    val filter = utils.CheckFilter(xt, ctx)
    val component = VerificationComponent

    val input =
      """|import stainless.lang._
         |
         |// Use with --functions=theorem --check-models
         |// Expect invalid result.
         |object TestFunctionsOption {
         |
         |  def skipped1: Boolean = { true }.holds
         |  def skipped2: Boolean = { false }.holds
         |
         |  def theorem(foo: Foo): Boolean = {
         |    foo.method == 42
         |  }.holds
         |
         |  /* NON SEALED */ abstract class Foo { def method: BigInt }
         |  case class Bar() extends Foo { override def method: BigInt = 0 }
         |
         |}
         |""".stripMargin

    val (_, program) = load(Seq(input), Some(filter))
    import program.trees._

    val theorem = program.symbols.lookup.get[FunDef]("TestFunctionsOption.theorem").get

    val run = component.run(extraction.pipeline)
    val analysis = run.apply(theorem.id, program.symbols)
    val stats = Await.result(analysis, Duration.Inf).toReport.stats

    // analysis.vrs foreach { r => info(r.toString) }

    assert(stats.valid   == 0, "No VC is expected to be valid for this test.")
    assert(stats.unknown == 0, "No VC is expected to be unknown for this test.")
    assert(stats.invalid == 1, "Exactly one VC is expected to be invalid for this test.")
  }
}

