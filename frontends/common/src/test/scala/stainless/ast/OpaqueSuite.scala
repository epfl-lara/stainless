/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package ast

import org.scalatest._
import scala.language.existentials

class OpaqueSuite extends FunSuite with InputUtils {

  val sources = List(
    """|import stainless.annotation._
       |object Opaque {
       |  @opaque
       |  def test(i: BigInt): BigInt = {
       |    require(i > 0)
       |    i + 1
       |  } ensuring (_ > i)
       |}""".stripMargin)

  implicit val ctx = stainless.TestContext.empty
  val (_, xlangProgram) = load(sources)
  val run = verification.VerificationComponent.run(extraction.pipeline)
  val program = inox.Program(run.trees)(run extract xlangProgram.symbols)
  val chooses = inox.transformers.ProgramEncoder(program)(verification.ChooseInjector(program))
  val encoded = solvers.InoxEncoder(chooses.targetProgram, ctx).targetProgram

  test("Encoding of opaque functions removes body") {
    import encoded.trees._
    val fd = encoded.symbols.functions.values.find(_.id.name == "test").get
    assert(!exprOps.exists {
      case Plus(_, _) => true
      case _ => false
    } (fd.fullBody))
  }

  test("Opaque functions lose body information") {
    import program.trees._
    import program.trees.dsl._

    val encoded = chooses.targetProgram
    val factory = solvers.SolverFactory(encoded, ctx)

    val fd = encoded.lookup[FunDef]("Opaque.test")
    val v = Variable.fresh("v", IntegerType())
    val clause = fd(v) === v + IntegerLiteral(1)

    assert(inox.solvers.SimpleSolverAPI(factory).solveVALID(clause) != Some(true))
  }
}
