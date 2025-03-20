/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class ImperativeSuite extends VerificationComponentTestSuite {

  override protected def optionsString(options: inox.Options): String = ""

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Unstable on 4.8.12, but works in non-incremental mode
    case "imperative/valid/WhileAsFun2" => Ignore
    // Succeeds most of the time, but unsuitable for CI due to its flakiness
    case "imperative/valid/i1306b" => Ignore

    case _ => super.filter(ctx, name)
  }

  import ImperativeSuite._

  testPosAll("imperative/valid", valid)

  testNegAll("imperative/invalid", invalid)
}
object ImperativeSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("imperative/valid")
  private lazy val invalid = ComponentTestSuite.loadPrograms("imperative/invalid")
}