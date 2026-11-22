/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest.funsuite.AnyFunSuite

/** The refinements of the fields of a sort, and the bodies of the functions over the sort that they call, may only
  * inspect the values of the sort (see `TypeChecker.onlyInspects`), and may not quantify over them (see
  * `inox.ast.Definitions.ensureStratifiedInvariant`).
  */
class FieldRefinementRecursionSuite extends AnyFunSuite with InputUtils {

  def source(defs: String, refinement: String = "p(v)") =
    s"""|import stainless.lang._
        |
        |object Test {
        |  sealed abstract class S
        |  case class A(x: BigInt) extends S
        |  case class B(o: Option[{ v: S with $refinement }]) extends S
        |
        |$defs
        |}""".stripMargin

  def isAccepted(defs: String, refinement: String = "p(v)"): Boolean = {
    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.given
    val (_, xlangProgram) = load(Seq(source(defs, refinement)))
    val run = VerificationComponent.run(extraction.pipeline)
    try {
      val program = inox.Program(run.trees)(run.extract(xlangProgram.symbols)._1)
      val sort = program.symbols.sorts.values.find(_.id.name == "S").get
      val fun = program.symbols.functions.values.find(_.id.name == "p").get
      val checker = TypeChecker(program, ctx)
      checker.checkADTRefinementRecursion(sort)
      checker.checkType(fun.id)
      program.symbols.ensureWellFormed
      true
    } catch {
      case _: inox.FatalError => false
      case _: run.trees.NotWellFormedException => false
    }
  }

  test("A function that only selects fields and tests constructors is accepted") {
    assert(isAccepted(
      """|  def get(s: S): BigInt = s match {
         |    case A(x) => x
         |    case B(Some(_)) => 1
         |    case B(None()) => 0
         |  }
         |  def p(s: S): Boolean = get(s) >= 0""".stripMargin))
  }

  test("A recursive function is rejected") {
    assert(!isAccepted(
      """|  def depth(s: S): BigInt = s match {
         |    case A(_) => 0
         |    case B(Some(s2)) => 1 + depth(s2)
         |    case B(None()) => 0
         |  }
         |  def p(s: S): Boolean = depth(s) >= 0""".stripMargin))
  }

  test("A function that quantifies over the sort is rejected") {
    assert(!isAccepted(
      """|  def p(s: S): Boolean = forall((t: S) => t != s)""".stripMargin))
  }

  test("A function that constructs values of the sort is rejected") {
    assert(!isAccepted(
      """|  def p(s: S): Boolean = s != A(0)""".stripMargin))
  }

  // The inline refinements are checked as the bodies of the functions they call, and as invariants

  val inlineDefs = "  def p(s: S): Boolean = true"

  test("An inline refinement that tests constructors is accepted") {
    assert(isAccepted(inlineDefs, "(v.isInstanceOf[A] || v.isInstanceOf[B])"))
  }

  test("An inline refinement that quantifies over the sort is rejected") {
    assert(!isAccepted(inlineDefs, "forall((t: S) => t != v)"))
  }

  test("An inline refinement that constructs values of the sort is rejected") {
    assert(!isAccepted(inlineDefs, "v != A(0)"))
  }

  test("A choose in a field type is rejected") {
    assert(!isAccepted(inlineDefs, "v != choose((a: A) => true)"))
  }

  // Inox rejects the chooses of values of the sort, once they are uninterpreted calls
  test("A choose in a function that a field type calls is accepted") {
    assert(isAccepted("  def p(s: S): Boolean = choose[BigInt]((n: BigInt) => n > 0) > 0"))
  }
}
