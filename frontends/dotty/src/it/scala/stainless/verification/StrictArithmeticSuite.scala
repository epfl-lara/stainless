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
  // extracted with strict arithmetic, as they are verified (see `configurations`)
  private val options = Seq(optStrictArithmetic(true))
  private lazy val valid = ComponentTestSuite.loadPrograms("strictarithmetic/valid", options = options)
  private lazy val invalid = ComponentTestSuite.loadPrograms("strictarithmetic/invalid", options = options)
}