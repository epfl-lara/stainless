/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class ImperativeSuite extends VerificationComponentTestSuite {

  override protected def optionsString(options: inox.Options): String = ""

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Unstable on 4.8.12, but works in non-incremental mode
    case "imperative/valid/WhileAsFun2" => Ignore

    case _ => super.filter(ctx, name)
  }

  testPosAll("imperative/valid")

  testNegAll("imperative/invalid")
}
