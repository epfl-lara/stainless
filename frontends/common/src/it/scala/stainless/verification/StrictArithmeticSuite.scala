/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class StrictArithmeticSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => Seq(optStrictArithmetic(true), optFailEarly(true)) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  import StrictArithmeticSuite._

  testPosAll("strictarithmetic/valid", valid)

  testNegAll("strictarithmetic/invalid", invalid)
}
object StrictArithmeticSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("strictarithmetic/valid")
  private lazy val invalid = ComponentTestSuite.loadPrograms("strictarithmetic/invalid")
}