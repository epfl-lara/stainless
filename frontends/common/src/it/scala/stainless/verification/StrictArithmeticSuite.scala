/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class StrictArithmeticSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => Seq(optStrictArithmetic(true), optFailEarly(true)) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  testPosAll("strictarithmetic/valid")

  testNegAll("strictarithmetic/invalid")
}
