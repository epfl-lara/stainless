/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import org.scalatest.funsuite.AnyFunSuite

import scala.util.control.NonFatal

class FunctionClosureSuite extends AnyFunSuite with InputUtils {

  val sources = List(
    """object InnerFunctions {
      |  def outer1(x: BigInt): Unit = {
      |    require(x >= 0) // Introduces a condition on x but should not be captured by inner1
      |    def inner1(): Unit = ()
      |  }
      |  def outer2(x: BigInt): Unit = {
      |    val y = x // Introduces a binding but neither should be captured by inner1
      |    val z = y // Ditto
      |    def inner2(a: BigInt): Unit = ()
      |  }
      |  def outer3(x: BigInt, y: BigInt, z: BigInt) = {
      |    require(0 <= x && x <= y)
      |    require(z >= 42)
      |    val a = x + 1
      |    def inner3A = { val aa = a + 1 }
      |    def inner3B = { val yy = y }
      |  }
      |} """.stripMargin,

  )

  val ctx: inox.Context = stainless.TestContext.empty
  import ctx.given
  val (_, xlangProgram) = load(sources)
  val run = verification.VerificationComponent.run(extraction.pipeline)
  val program = inox.Program(run.trees)(run extract xlangProgram.symbols)

  import stainless.trees._

  /* Mini DSL for testing purposes */

  def funDef(name: String) = program.lookup[FunDef](name)

  test("FunctionClosure does not close over PC variables not occurring in inner functions") {
    val inner1 = funDef("InnerFunctions.inner1")
    val inner2 = funDef("InnerFunctions.inner2")
    val inner3A = funDef("InnerFunctions.inner3A")
    val inner3B = funDef("InnerFunctions.inner3B")
    assert(inner1.params.isEmpty)
    assert(inner2.params.size == 1)
    assert(inner3A.params.map(_.id.name) == Seq("x", "y"))
    assert(inner3B.params.map(_.id.name) == Seq("x", "y"))
  }
}
